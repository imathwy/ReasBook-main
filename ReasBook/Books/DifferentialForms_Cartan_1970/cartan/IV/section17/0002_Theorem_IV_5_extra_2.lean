import DifferentialForms_Cartan_1970.IV.section14.«0002_Definition_IV_2_extra_2»
import DifferentialForms_Cartan_1970.IV.section17.«0001_Definition_IV_5_extra_1»
import DifferentialForms_Cartan_1970.IV.section17.«0002_Theorem_IV_5_extra_2».DimensionTransport
import DifferentialForms_Cartan_1970.IV.section17.«0002_Theorem_IV_5_extra_2».TransportedSlices
import DifferentialForms_Cartan_1970.IV.section17.«0002_Theorem_IV_5_extra_2».WeightedTransport
import DifferentialForms_Cartan_1970.IV.section17.«0002_Theorem_IV_5_extra_2».TransportedCauchyTransform
import DifferentialForms_Cartan_1970.IV.section17.«0002_Theorem_IV_5_extra_2».BoundaryCauchySeries
import DifferentialForms_Cartan_1970.IV.section17.«0002_Theorem_IV_5_extra_2».ParametricPowerSeries
import DifferentialForms_Cartan_1970.IV.section17.«0002_Theorem_IV_5_extra_2».LocalSeriesBounds
import DifferentialForms_Cartan_1970.IV.section17.«0002_Theorem_IV_5_extra_2».HigherDimensionalHartogs

open scoped BigOperators

section

variable {n : ℕ} {D : Set (Fin n → ℂ)} {f : (Fin n → ℂ) → ℂ}

/-- Helper for Theorem IV.5-extra-2: after transporting `Fin (m + 2) → ℂ` to
`(Fin (m + 1) → ℂ) × ℂ`, the separate analyticity hypotheses become the product-coordinate
separate analyticity package expected by the higher-dimensional frontier theorem. -/
lemma transportedProductSeparateAnalytic_local
    {m : ℕ} {D : Set (Fin (m + 2) → ℂ)} {f : (Fin (m + 2) → ℂ) → ℂ}
    (ih : ∀ {D' : Set (Fin (m + 1) → ℂ)} {f' : (Fin (m + 1) → ℂ) → ℂ},
      IsOpen D' →
      (∀ z ∈ D', ∀ i : Fin (m + 1), AnalyticAt ℂ (fun w ↦ f' (Function.update z i w)) (z i)) →
      AnalyticOnNhd ℂ f' D')
    (hD : IsOpen D)
    (hsep : ∀ z ∈ D, ∀ i : Fin (m + 2), AnalyticAt ℂ (fun w ↦ f (Function.update z i w)) (z i)) :
    let e := Fin.succFunEquiv ℂ (m + 1)
    let g : (Fin (m + 1) → ℂ) × ℂ → ℂ := f ∘ e.symm
    ∀ p ∈ {p : (Fin (m + 1) → ℂ) × ℂ | e.symm p ∈ D},
      AnalyticAt ℂ (fun x : Fin (m + 1) → ℂ ↦ g (x, p.2)) p.1 ∧
        AnalyticAt ℂ (fun w : ℂ ↦ g (p.1, w)) p.2 := by
  dsimp
  intro p hp
  constructor
  · -- The block slice is exactly the transported fixed-last slice.
    have hOn :
        AnalyticOnNhd ℂ
          (fun x : Fin (m + 1) → ℂ ↦ (f ∘ (Fin.succFunEquiv ℂ (m + 1)).symm) (x, p.2))
          {x | (Fin.succFunEquiv ℂ (m + 1)).symm (x, p.2) ∈ D} := by
      simpa [Function.comp] using
        transportedFixedLastSlice_analyticOnNhd ih hD hsep p.2
    exact hOn p.1 hp
  · -- The last slice is exactly the transported last-coordinate slice.
    simpa [Function.comp] using
      transportedLastSlice_analyticAt hsep hp

/-- Helper for Theorem IV.5-extra-2: the inverse transported-coordinate map from
`(Fin (m + 1) → ℂ) × ℂ` back to `Fin (m + 2) → ℂ` is jointly analytic. -/
lemma analyticAt_succFunEquivSymm_local
    {m : ℕ} (p : (Fin (m + 1) → ℂ) × ℂ) :
    AnalyticAt ℂ (Fin.succFunEquiv ℂ (m + 1)).symm p := by
  -- Prove analyticity coordinatewise: the inverse transport reads the block coordinates from
  -- `fst` and the last coordinate from `snd`.
  refine AnalyticAt.pi fun j ↦ ?_
  refine Fin.lastCases ?_ ?_ j
  · have hLastCoord :
        (fun q : (Fin (m + 1) → ℂ) × ℂ ↦
          (Fin.succFunEquiv ℂ (m + 1)).symm q (Fin.last (m + 1))) =
          (fun q : (Fin (m + 1) → ℂ) × ℂ ↦ q.2) := by
      funext q
      have hsymm :
          (Fin.succFunEquiv ℂ (m + 1)).symm q = Fin.append q.1 (uniqueElim q.2 : Fin 1 → ℂ) := by
        rfl
      have hcoord :
          (Fin.succFunEquiv ℂ (m + 1)).symm q (Fin.last (m + 1)) =
            Fin.append q.1 (uniqueElim q.2 : Fin 1 → ℂ) (Fin.last (m + 1)) := by
        exact congrArg (fun x : Fin (m + 2) → ℂ ↦ x (Fin.last (m + 1))) hsymm
      calc
        (Fin.succFunEquiv ℂ (m + 1)).symm q (Fin.last (m + 1))
            = Fin.append q.1 (uniqueElim q.2 : Fin 1 → ℂ) (Fin.last (m + 1)) := hcoord
        _ = (uniqueElim q.2 : Fin 1 → ℂ) 0 := by
              exact Fin.append_right q.1 (uniqueElim q.2 : Fin 1 → ℂ) (0 : Fin 1)
        _ = q.2 := by
              simp
    rw [hLastCoord]
    simpa using
      (analyticAt_snd : AnalyticAt ℂ (fun q : (Fin (m + 1) → ℂ) × ℂ ↦ q.2) p)
  · intro k
    let projk : (Fin (m + 1) → ℂ) →L[ℂ] ℂ := ContinuousLinearMap.proj k
    have hproj :
        AnalyticAt ℂ (fun x : Fin (m + 1) → ℂ ↦ x k) p.1 := by
      simpa using
        (ContinuousLinearMap.analyticAt projk p.1)
    have hBlockCoord :
        (fun q : (Fin (m + 1) → ℂ) × ℂ ↦
          (Fin.succFunEquiv ℂ (m + 1)).symm q k.castSucc) =
          (fun q : (Fin (m + 1) → ℂ) × ℂ ↦ q.1 k) := by
      funext q
      have hsymm :
          (Fin.succFunEquiv ℂ (m + 1)).symm q = Fin.append q.1 (uniqueElim q.2 : Fin 1 → ℂ) := by
        rfl
      have hcoord :
          (Fin.succFunEquiv ℂ (m + 1)).symm q k.castSucc =
            Fin.append q.1 (uniqueElim q.2 : Fin 1 → ℂ) k.castSucc := by
        exact congrArg (fun x : Fin (m + 2) → ℂ ↦ x k.castSucc) hsymm
      calc
        (Fin.succFunEquiv ℂ (m + 1)).symm q k.castSucc
            = Fin.append q.1 (uniqueElim q.2 : Fin 1 → ℂ) k.castSucc := hcoord
        _ = q.1 k := by
              exact Fin.append_left q.1 (uniqueElim q.2 : Fin 1 → ℂ) k
    rw [hBlockCoord]
    simpa using
      hproj.comp
        (analyticAt_fst : AnalyticAt ℂ (fun q : (Fin (m + 1) → ℂ) × ℂ ↦ q.1) p)

/-- Helper for Theorem IV.5-extra-2: any Hartogs owner on `Fin (m + 2) → ℂ` transports to the
product-coordinate callback on `((Fin (m + 1) → ℂ) × ℂ)`. -/
lemma productHartogs_ofSuccHartogs_local
    {m : ℕ}
    (hartogsSucc :
      ∀ {D : Set (Fin (m + 2) → ℂ)} {F : (Fin (m + 2) → ℂ) → ℂ},
        IsOpen D →
        (∀ z ∈ D, ∀ i : Fin (m + 2), AnalyticAt ℂ (fun w ↦ F (Function.update z i w)) (z i)) →
        AnalyticOnNhd ℂ F D)
    {Dprod : Set ((Fin (m + 1) → ℂ) × ℂ)} {Gprod : ((Fin (m + 1) → ℂ) × ℂ) → ℂ}
    (hDprod : IsOpen Dprod)
    (hsepProd :
      ∀ p ∈ Dprod,
        AnalyticAt ℂ (fun x : Fin (m + 1) → ℂ ↦ Gprod (x, p.2)) p.1 ∧
          AnalyticAt ℂ (fun u : ℂ ↦ Gprod (p.1, u)) p.2) :
    AnalyticOnNhd ℂ Gprod Dprod := by
  let e := Fin.succFunEquiv ℂ (m + 1)
  let F : (Fin (m + 2) → ℂ) → ℂ := Gprod ∘ e
  let D : Set (Fin (m + 2) → ℂ) := {z | e z ∈ Dprod}
  have heCont : Continuous e := by
    have hBlock :
        Continuous (fun z : Fin (m + 2) → ℂ ↦ fun i : Fin (m + 1) ↦ z (Fin.castAdd 1 i)) := by
      refine continuous_pi fun i ↦ ?_
      simpa using
        (continuous_apply (Fin.castAdd 1 i) :
          Continuous fun z : Fin (m + 2) → ℂ ↦ z (Fin.castAdd 1 i))
    have hLast :
        Continuous (fun z : Fin (m + 2) → ℂ ↦ z (Fin.last (m + 1))) := by
      simpa using
        (continuous_apply (Fin.last (m + 1)) :
          Continuous fun z : Fin (m + 2) → ℂ ↦ z (Fin.last (m + 1)))
    change Continuous (fun z : Fin (m + 2) → ℂ ↦
      ((fun i : Fin (m + 1) ↦ z (Fin.castAdd 1 i)), z (Fin.last (m + 1))))
    simpa [e, Fin.succFunEquiv_apply] using hBlock.prodMk hLast
  have hD : IsOpen D := hDprod.preimage heCont
  have hsep :
      ∀ z ∈ D, ∀ i : Fin (m + 2), AnalyticAt ℂ (fun w ↦ F (Function.update z i w)) (z i) := by
    intro z hz i
    have hzProd : e z ∈ Dprod := hz
    refine Fin.lastCases ?_ ?_ i
    · have hLast : AnalyticAt ℂ (fun u : ℂ ↦ Gprod ((e z).1, u)) (e z).2 :=
        (hsepProd (e z) hzProd).2
      have hLastEq :
          (fun u ↦ F (Function.update z (Fin.last (m + 1)) u)) =
            (fun u ↦ Gprod ((e z).1, u)) := by
        funext u
        apply congrArg Gprod
        refine Prod.ext ?_ ?_
        · funext j
          have hne : Fin.castAdd 1 j ≠ Fin.last (m + 1) := by
            intro h
            exact Nat.ne_of_lt j.is_lt
              (by simpa [Fin.val_castAdd, Fin.val_last] using congrArg Fin.val h)
          simp [e, Fin.succFunEquiv_apply, Function.update, hne]
        · by_cases h : Fin.natAdd (m + 1) 0 = Fin.last (m + 1)
          · simp [e, Fin.succFunEquiv_apply, Function.update, h]
          · exfalso
            exact h rfl
      rw [hLastEq]
      simpa [e, Fin.succFunEquiv_apply] using hLast
    · intro iBlock
      have hBlockFamily :
          AnalyticAt ℂ (fun x : Fin (m + 1) → ℂ ↦ Gprod (x, (e z).2)) (e z).1 :=
        (hsepProd (e z) hzProd).1
      have hInsert :
          AnalyticAt ℂ (fun u : ℂ ↦ Function.update (e z).1 iBlock u) ((e z).1 iBlock) := by
        simpa using analyticAt_update_coordinate (e z).1 iBlock
      have hBlock :
          AnalyticAt ℂ (fun u ↦ Gprod (Function.update (e z).1 iBlock u, (e z).2))
            ((e z).1 iBlock) := by
        have hCenter :
            (fun u : ℂ ↦ Function.update (e z).1 iBlock u) ((e z).1 iBlock) = (e z).1 := by
          simp
        simpa using
          hBlockFamily.comp_of_eq hInsert hCenter
      have hBlockEq :
          (fun u ↦ F (Function.update z iBlock.castSucc u)) =
            (fun u ↦ Gprod (Function.update (e z).1 iBlock u, (e z).2)) := by
        funext u
        apply congrArg Gprod
        refine Prod.ext ?_ ?_
        · funext j
          by_cases hj : j = iBlock
          · subst j
            calc
              (e (Function.update z iBlock.castSucc u)).1 iBlock
                  = (Function.update z iBlock.castSucc u) (Fin.castAdd 1 iBlock) := by
                    simp [e, Fin.succFunEquiv_apply]
              _ = u := by
                    rw [show Fin.castAdd 1 iBlock = iBlock.castSucc from rfl]
                    simp [Function.update]
              _ = (Function.update (e z).1 iBlock u, (e z).2).1 iBlock := by
                    simp [Function.update]
          · have hne : Fin.castAdd 1 j ≠ iBlock.castSucc := by
              intro h
              apply hj
              exact Fin.ext (by simpa [Fin.val_castAdd, Fin.val_castSucc] using congrArg Fin.val h)
            simp [e, Fin.succFunEquiv_apply, Function.update, hj, hne]
        · have hne : Fin.natAdd (m + 1) 0 ≠ iBlock.castSucc := by
            intro h
            exact Nat.ne_of_lt iBlock.is_lt
              (by simpa [Fin.val_natAdd, Fin.val_castSucc] using (congrArg Fin.val h).symm)
          simp [e, Fin.succFunEquiv_apply, Function.update, hne]
      rw [hBlockEq]
      simpa [e, Fin.succFunEquiv_apply] using hBlock
  have hFOn : AnalyticOnNhd ℂ F D := hartogsSucc hD hsep
  intro p hp
  have hpD : e.symm p ∈ D := by
    change e (e.symm p) ∈ Dprod
    simpa [e] using hp
  have hFAt : AnalyticAt ℂ F (e.symm p) := hFOn (e.symm p) hpD
  have hSymmAt : AnalyticAt ℂ e.symm p := analyticAt_succFunEquivSymm_local p
  have hBack :
      (fun q : (Fin (m + 1) → ℂ) × ℂ ↦ F (e.symm q)) = Gprod := by
    funext q
    simp [F, e]
  -- Compose the transported `Fin (m + 2)` germ back with the analytic inverse coordinate map.
  rw [← hBack]
  exact hFAt.comp hSymmAt

/-- Helper for Theorem IV.5-extra-2: the independent Hartogs owner on
`(Fin (m + 1) → ℂ) × ℂ` is the remaining product-domain frontier needed by the wrapper file. -/
lemma exists_productCylinder_subset_of_isOpen_local
    {m : ℕ}
    {D : Set ((Fin (m + 1) → ℂ) × ℂ)}
    (hD : IsOpen D) {p : (Fin (m + 1) → ℂ) × ℂ} (hp : p ∈ D) :
    ∃ ρ > 0, Metric.ball p.1 (ρ / 2) ×ˢ Metric.closedBall p.2 (ρ / 2) ⊆ D := by
  obtain ⟨ρ, hρpos, hρsub⟩ := Metric.isOpen_iff.mp hD p hp
  refine ⟨ρ, hρpos, ?_⟩
  intro q hq
  have hx : dist q.1 p.1 < ρ / 2 := by
    simpa using hq.1
  have hw : dist q.2 p.2 ≤ ρ / 2 := by
    simpa [Metric.mem_closedBall] using hq.2
  have hhalf_lt : ρ / 2 < ρ := by
    linarith
  have hqBall : q ∈ Metric.ball p ρ := by
    have hmax : max (dist q.1 p.1) (dist q.2 p.2) < ρ := by
      exact max_lt_iff.mpr ⟨lt_trans hx hhalf_lt, lt_of_le_of_lt hw hhalf_lt⟩
    simpa [Metric.mem_ball, Prod.dist_eq] using hmax
  exact hρsub hqBall

/-- Helper for Theorem IV.5-extra-2: on a product cylinder, the explicit last-variable Cauchy
transform agrees with the original function throughout the interior last disc. -/
lemma productLastCauchyTransform_eqOn_ball_local
    {m : ℕ}
    {D : Set ((Fin (m + 1) → ℂ) × ℂ)} {G : ((Fin (m + 1) → ℂ) × ℂ) → ℂ}
    {p : (Fin (m + 1) → ℂ) × ℂ} {ρ : ℝ}
    (hsep : ∀ q ∈ D,
      AnalyticAt ℂ (fun x : Fin (m + 1) → ℂ ↦ G (x, q.2)) q.1 ∧
        AnalyticAt ℂ (fun u : ℂ ↦ G (q.1, u)) q.2)
    (hcyl : Metric.ball p.1 (ρ / 2) ×ˢ Metric.closedBall p.2 (ρ / 2) ⊆ D) :
    ∀ x ∈ Metric.ball p.1 (ρ / 2),
      Set.EqOn
        (fun w ↦ G (x, w))
        (fun w ↦
          ((2 * Real.pi * Complex.I : ℂ)⁻¹ •
            ∮ ζ in C(p.2, ρ / 2), (ζ - w)⁻¹ • G (x, ζ)))
        (Metric.ball p.2 (ρ / 2)) := by
  intro x hx w hw
  have hslice :
      AnalyticOnNhd ℂ (fun u ↦ G (x, u)) (Metric.closedBall p.2 (ρ / 2)) := by
    intro u hu
    exact (hsep (x, u) (hcyl ⟨hx, hu⟩)).2
  have hdiff :
      DifferentiableOn ℂ (fun u ↦ G (x, u)) (Metric.closedBall p.2 (ρ / 2)) :=
    hslice.differentiableOn
  have hdiffCl :
      DiffContOnCl ℂ (fun u ↦ G (x, u)) (Metric.ball p.2 (ρ / 2)) :=
    hdiff.diffContOnCl_ball (by intro u hu; exact hu)
  -- Evaluate the fixed-block last slice by the one-variable Cauchy formula on the working disc.
  simpa only [smul_eq_mul, div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using
    (hdiffCl.two_pi_i_inv_smul_circleIntegral_sub_inv_smul hw).symm

/-- Helper for Theorem IV.5-extra-2: on the common smaller product ball, the normalized
`cauchyPowerSeries` model already agrees pointwise with the original function. -/
lemma normalizedProductCauchySeries_eqOn_smallBall_local
    {m : ℕ}
    {D : Set ((Fin (m + 1) → ℂ) × ℂ)} {G : ((Fin (m + 1) → ℂ) × ℂ) → ℂ}
    {p : (Fin (m + 1) → ℂ) × ℂ} {ρ : ℝ}
    (hρpos : 0 < ρ)
    (hsep : ∀ q ∈ D,
      AnalyticAt ℂ (fun x : Fin (m + 1) → ℂ ↦ G (x, q.2)) q.1 ∧
        AnalyticAt ℂ (fun u : ℂ ↦ G (q.1, u)) q.2)
    (hcyl : Metric.ball p.1 (ρ / 2) ×ˢ Metric.closedBall p.2 (ρ / 2) ⊆ D) :
    Set.EqOn
      (fun q : (Fin (m + 1) → ℂ) × ℂ ↦
        ∑' n : ℕ,
          (cauchyPowerSeries (fun ζ ↦ G (q.1, ζ)) p.2 (ρ / 2)).coeff n * (q.2 - p.2) ^ n)
      G
      (Metric.ball p (ρ / 8)) := by
  intro q hq
  have hqdist : dist q p < ρ / 8 := by
    simpa [Metric.mem_ball] using hq
  have hprod : max (dist q.1 p.1) (dist q.2 p.2) < ρ / 8 := by
    simpa [Prod.dist_eq] using hqdist
  have hqBlock_eighth : dist q.1 p.1 < ρ / 8 := (max_lt_iff.mp hprod).1
  have hqLast_eighth : dist q.2 p.2 < ρ / 8 := (max_lt_iff.mp hprod).2
  have heighth_lt_half : ρ / 8 < ρ / 2 := by
    linarith
  have heighth_lt_quarter : ρ / 8 < ρ / 4 := by
    linarith
  have hqBlock : q.1 ∈ Metric.ball p.1 (ρ / 2) := by
    simpa [Metric.mem_ball] using lt_trans hqBlock_eighth heighth_lt_half
  have hqLast : q.2 ∈ Metric.ball p.2 (ρ / 4) := by
    simpa [Metric.mem_ball] using lt_trans hqLast_eighth heighth_lt_quarter
  have hslice :
      AnalyticOnNhd ℂ (fun w ↦ G (q.1, w)) (Metric.closedBall p.2 (ρ / 2)) := by
    intro w hw
    exact (hsep (q.1, w) (hcyl ⟨hqBlock, hw⟩)).2
  have hCircle :
      CircleIntegrable (fun ζ ↦ G (q.1, ζ)) p.2 (ρ / 2) := by
    have hcont :
        ContinuousOn (fun ζ ↦ G (q.1, ζ)) (Metric.sphere p.2 (ρ / 2)) := by
      -- Restrict the analytic slice once to the boundary circle to obtain integrability.
      exact hslice.continuousOn.mono Metric.sphere_subset_closedBall
    exact hcont.circleIntegrable (by positivity)
  have hqLast_half : ‖q.2 - p.2‖ < ρ / 2 := by
    simpa [dist_eq_norm] using lt_trans hqLast_eighth heighth_lt_half
  have hSeriesEq :
      ((2 * Real.pi * Complex.I : ℂ)⁻¹ •
        ∮ ζ in C(p.2, ρ / 2), (ζ - q.2)⁻¹ • G (q.1, ζ)) =
      (cauchyPowerSeries (fun ζ ↦ G (q.1, ζ)) p.2 (ρ / 2)).sum (q.2 - p.2) := by
    -- Evaluate the canonical scalar Cauchy power series at the true last-coordinate displacement.
    simpa [smul_eq_mul, FormalMultilinearSeries.sum, add_sub_cancel] using
      (sum_cauchyPowerSeries_eq_integral
        hCircle hqLast_half).symm
  have hTsumEq :
      (cauchyPowerSeries (fun ζ ↦ G (q.1, ζ)) p.2 (ρ / 2)).sum (q.2 - p.2) =
      ∑' n : ℕ,
        (cauchyPowerSeries (fun ζ ↦ G (q.1, ζ)) p.2 (ρ / 2)).coeff n * (q.2 - p.2) ^ n := by
    simpa using
      cauchyPowerSeries_sum_eq_tsum_coeff
  calc
    ∑' n : ℕ, (cauchyPowerSeries (fun ζ ↦ G (q.1, ζ)) p.2 (ρ / 2)).coeff n * (q.2 - p.2) ^ n
        =
          (cauchyPowerSeries (fun ζ ↦ G (q.1, ζ)) p.2 (ρ / 2)).sum (q.2 - p.2) := by
            symm
            exact hTsumEq
    _ = ((2 * Real.pi * Complex.I : ℂ)⁻¹ •
          ∮ ζ in C(p.2, ρ / 2), (ζ - q.2)⁻¹ • G (q.1, ζ)) := by
            exact hSeriesEq.symm
    _ = G q := by
          simpa using
            (productLastCauchyTransform_eqOn_ball_local
              hsep hcyl q.1 hqBlock
              (by simpa [Metric.mem_ball] using lt_trans hqLast_eighth heighth_lt_half)).symm

/-- Helper for Theorem IV.5-extra-2: each last-variable Cauchy coefficient along a coordinate slice
has the expected centered circle-integral normal form. -/
lemma productCauchyCoeffSlice_eq_centeredIntegral_local
    {m : ℕ}
    {G : ((Fin (m + 1) → ℂ) × ℂ) → ℂ}
    {p : (Fin (m + 1) → ℂ) × ℂ} {ρ : ℝ}
    (n : ℕ) (x : Fin (m + 1) → ℂ) (i : Fin (m + 1)) (u : ℂ) :
    (cauchyPowerSeries (fun ζ ↦ G (Function.update x i u, ζ)) p.2 (ρ / 2)).coeff n =
      ((2 * Real.pi * Complex.I : ℂ)⁻¹ •
        ∮ ζ in C(p.2, ρ / 2),
          ((ζ - p.2)⁻¹) ^ n * ((ζ - p.2)⁻¹ * G (Function.update x i u, ζ))) := by
  -- Normalize the coefficient once to the centered boundary integral spelling used by the direct
  -- closeout route.
  have hCoeff :
      (cauchyPowerSeries (fun ζ ↦ G (Function.update x i u, ζ)) p.2 (ρ / 2)).coeff n =
        ((2 * Real.pi * Complex.I : ℂ)⁻¹ •
          ∮ ζ in C(p.2, ρ / 2), ((ζ - p.2)⁻¹) ^ n • (ζ - p.2)⁻¹ • G (Function.update x i u, ζ)) :=
    cauchyPowerSeries_coeff_eq_centeredIntegral n
  simpa [smul_eq_mul, mul_assoc, mul_left_comm, mul_comm] using hCoeff

/-- Helper for Theorem IV.5-extra-2: once the block point is frozen inside the smaller closed ball,
the weighted boundary slice is continuous on the distinguished outer circle. This isolates the
easy one-variable continuity input from the harder joint-torus continuity frontier. -/
lemma weightedBoundarySlice_continuousOn_sphere_local
    {m : ℕ}
    {D : Set ((Fin (m + 1) → ℂ) × ℂ)} {G : ((Fin (m + 1) → ℂ) × ℂ) → ℂ}
    {p : (Fin (m + 1) → ℂ) × ℂ} {ρ : ℝ}
    (hρpos : 0 < ρ)
    (hcyl : Metric.ball p.1 (ρ / 2) ×ˢ Metric.closedBall p.2 (ρ / 2) ⊆ D)
    (hsep : ∀ q ∈ D,
      AnalyticAt ℂ (fun x : Fin (m + 1) → ℂ ↦ G (x, q.2)) q.1 ∧
        AnalyticAt ℂ (fun u : ℂ ↦ G (q.1, u)) q.2)
    {n : ℕ} {x : Fin (m + 1) → ℂ}
    (hx : x ∈ Metric.closedBall p.1 (ρ / 8)) :
    ContinuousOn
      (fun ζ ↦ ((ζ - p.2)⁻¹) ^ n * ((ζ - p.2)⁻¹ * G (x, ζ)))
      (Metric.sphere p.2 (ρ / 2)) := by
  have hbase :
      ContinuousOn (fun ζ ↦ G (x, ζ)) (Metric.sphere p.2 (ρ / 2)) := by
    -- Read the unweighted boundary continuity from the compact-circle slice theorem first.
    exact
      prodBoundarySlice_continuousOn_sphere_closedBall
        (m := m) (D := D) (G := G) (p := p) (ρ := ρ) hρpos hsep hcyl x hx
  have hkernelNe :
      ∀ ζ ∈ Metric.sphere p.2 (ρ / 2), ζ - p.2 ≠ 0 := by
    intro ζ hζ
    intro hzero
    have hdist : dist ζ p.2 = ρ / 2 := by
      simpa [Metric.mem_sphere, dist_eq_norm] using hζ
    have hzeroDist : dist ζ p.2 = 0 := by
      simp [dist_eq_norm, hzero]
    linarith
  have hkernelCont :
      ContinuousOn (fun ζ : ℂ ↦ (ζ - p.2)⁻¹) (Metric.sphere p.2 (ρ / 2)) :=
    (continuousOn_id.sub continuousOn_const).inv₀ hkernelNe
  -- Multiply the pole-free kernel factors by the already-continuous boundary values.
  exact (hkernelCont.pow n).mul (hkernelCont.mul hbase)

/-- Helper for Theorem IV.5-extra-2: in the one-block-coordinate case, the weighted auxiliary
`Fin 2` domain is open because it is only the original product domain together with the visible
pole-avoidance condition on the second coordinate. -/
lemma weightedBoundaryAuxFin2Domain_open_local
    {D : Set ((Fin 1 → ℂ) × ℂ)} {w0 : ℂ}
    (hD : IsOpen D) :
    IsOpen {y : Fin 2 → ℂ | ((fun _ : Fin 1 => y 0), y 1) ∈ D ∧ y 1 ≠ w0} := by
  have hpackCont :
      Continuous (fun y : Fin 2 → ℂ ↦ ((fun _ : Fin 1 => y 0), y 1)) := by
    refine (continuous_pi fun _ ↦ continuous_apply 0).prodMk (continuous_apply 1)
  have hmemOpen :
      IsOpen {y : Fin 2 → ℂ | ((fun _ : Fin 1 => y 0), y 1) ∈ D} := by
    exact hD.preimage hpackCont
  have hneOpen : IsOpen {y : Fin 2 → ℂ | y 1 ≠ w0} := by
    change IsOpen ((fun y : Fin 2 → ℂ ↦ y 1) ⁻¹' ({w0}ᶜ))
    exact (isClosed_singleton.preimage (continuous_apply 1)).isOpen_compl
  -- Intersect the transported domain condition with the explicit pole-avoidance condition.
  simpa [Set.setOf_and] using hmemOpen.inter hneOpen

/-- Helper for Theorem IV.5-extra-2: in the one-block-coordinate case, the weighted auxiliary
`Fin 2` owner already has separately analytic coordinate slices on its auxiliary domain. The only
remaining base-case frontier is the nonrecursive `Fin 2` Hartogs closeout itself. -/
lemma weightedBoundaryAuxFin2Separate_local
    {D : Set ((Fin 1 → ℂ) × ℂ)} {G : ((Fin 1 → ℂ) × ℂ) → ℂ}
    {w0 : ℂ} {n : ℕ}
    (hsep : ∀ q ∈ D,
      AnalyticAt ℂ (fun x : Fin 1 → ℂ ↦ G (x, q.2)) q.1 ∧
        AnalyticAt ℂ (fun u : ℂ ↦ G (q.1, u)) q.2) :
    let Daux : Set (Fin 2 → ℂ) := {y | ((fun _ : Fin 1 => y 0), y 1) ∈ D ∧ y 1 ≠ w0}
    let Haux : (Fin 2 → ℂ) → ℂ := fun y ↦
      ((y 1 - w0)⁻¹) ^ n * ((y 1 - w0)⁻¹ * G ((fun _ : Fin 1 => y 0), y 1))
    ∀ y ∈ Daux, ∀ k : Fin 2,
      AnalyticAt ℂ (fun w ↦ Haux (Function.update y k w)) (y k) := by
  dsimp
  intro y hy k
  rcases hy with ⟨hyD, hyNe⟩
  fin_cases k
  · change
      AnalyticAt ℂ
        (fun w ↦
          ((y 1 - w0)⁻¹) ^ n * ((y 1 - w0)⁻¹ * G ((fun _ : Fin 1 => w), y 1)))
        (y 0)
    have hBlockAt :
        AnalyticAt ℂ (fun x : Fin 1 → ℂ ↦ G (x, y 1)) (fun _ : Fin 1 => y 0) :=
      (hsep _ hyD).1
    have hPackAt : AnalyticAt ℂ (fun w : ℂ ↦ fun _ : Fin 1 => w) (y 0) := by
      refine AnalyticAt.pi fun j ↦ ?_
      fin_cases j
      simpa using (analyticAt_id : AnalyticAt ℂ (fun w : ℂ ↦ w) (y 0))
    have hSliceAt :
        AnalyticAt ℂ (fun w ↦ G ((fun _ : Fin 1 => w), y 1)) (y 0) := by
      simpa using hBlockAt.comp hPackAt
    -- The weighted block slice is the analytic block slice multiplied by fixed pole-free factors.
    simpa [mul_assoc] using (analyticAt_const.mul (analyticAt_const.mul hSliceAt))
  · change
      AnalyticAt ℂ
        (fun w ↦ ((w - w0)⁻¹) ^ n * ((w - w0)⁻¹ * G ((fun _ : Fin 1 => y 0), w)))
        (y 1)
    have hGLast :
        AnalyticAt ℂ (fun w : ℂ ↦ G ((fun _ : Fin 1 => y 0), w)) (y 1) :=
      (hsep _ hyD).2
    have hKernel :
        AnalyticAt ℂ (fun w : ℂ ↦ (w - w0)⁻¹) (y 1) := by
      exact (analyticAt_id.sub analyticAt_const).inv (by simpa using sub_ne_zero.mpr hyNe)
    -- The second coordinate is the genuine last-variable slice, again multiplied by the same
    -- explicit pole-free factors.
    exact (hKernel.pow n).mul (hKernel.mul hGLast)

/-- Helper for Theorem IV.5-extra-2: once the missing `Fin 2` Hartogs callback is available, the
base-case weighted torus germ is just the auxiliary `Fin 2` owner pulled back along the swap map
`(ζ,u) ↦ ![u,ζ]`. -/
lemma weightedBoundarySliceAnalyticAt_base_ofFin2Hartogs_local
    (fin2Hartogs :
      ∀ {D2 : Set (Fin 2 → ℂ)} {F : (Fin 2 → ℂ) → ℂ},
        IsOpen D2 →
        (∀ z ∈ D2, ∀ i : Fin 2, AnalyticAt ℂ (fun w ↦ F (Function.update z i w)) (z i)) →
        AnalyticOnNhd ℂ F D2)
    {D : Set ((Fin 1 → ℂ) × ℂ)} {G : ((Fin 1 → ℂ) × ℂ) → ℂ}
    {p : (Fin 1 → ℂ) × ℂ} {n : ℕ} {x : Fin 1 → ℂ} {q : ℂ × ℂ}
    (hD : IsOpen D)
    (hsep : ∀ y ∈ D,
      AnalyticAt ℂ (fun z : Fin 1 → ℂ ↦ G (z, y.2)) y.1 ∧
        AnalyticAt ℂ (fun u : ℂ ↦ G (y.1, u)) y.2)
    (hqD : (Function.update x 0 q.2, q.1) ∈ D)
    (hqNe : q.1 ≠ p.2) :
    AnalyticAt ℂ
      (Function.uncurry fun ζ u ↦
        ((ζ - p.2)⁻¹) ^ n * ((ζ - p.2)⁻¹ * G (Function.update x 0 u, ζ)))
      q := by
  let Daux : Set (Fin 2 → ℂ) := {y | ((fun _ : Fin 1 => y 0), y 1) ∈ D ∧ y 1 ≠ p.2}
  let Haux : (Fin 2 → ℂ) → ℂ := fun y ↦
    ((y 1 - p.2)⁻¹) ^ n * ((y 1 - p.2)⁻¹ * G ((fun _ : Fin 1 => y 0), y 1))
  let φ : ℂ × ℂ → Fin 2 → ℂ := fun r ↦ ![r.2, r.1]
  have hDauxOpen : IsOpen Daux := by
    -- Reuse the already-isolated auxiliary-domain openness proof instead of rebuilding it here.
    simpa [Daux] using
      weightedBoundaryAuxFin2Domain_open_local (D := D) (w0 := p.2) hD
  have hHauxSep :
      ∀ y ∈ Daux, ∀ k : Fin 2,
        AnalyticAt ℂ (fun w ↦ Haux (Function.update y k w)) (y k) := by
    -- The coordinate-slice analyticity of the auxiliary owner is already packaged above.
    simpa [Daux, Haux] using
      weightedBoundaryAuxFin2Separate_local (D := D) (G := G) (w0 := p.2) (n := n) hsep
  have hφAt : AnalyticAt ℂ φ q := by
    -- The pullback map is exactly the analytic coordinate swap on `ℂ × ℂ`.
    exact (analyticOnNhd_fin2Swap (s := Set.univ)) q (by simp)
  have hUpdateConst' (u : ℂ) :
      Function.update x 0 u = (fun _ : Fin 1 => u) := by
    funext j
    fin_cases j
    simp [Function.update]
  have hφMem : φ q ∈ Daux := by
    refine ⟨?_, ?_⟩
    · change ((fun _ : Fin 1 => q.2), q.1) ∈ D
      rw [← hUpdateConst' q.2]
      exact hqD
    · simpa [φ] using hqNe
  have hKernel :
      (fun r : ℂ × ℂ ↦ Haux (φ r)) =
        Function.uncurry
          (fun ζ u ↦
            ((ζ - p.2)⁻¹) ^ n * ((ζ - p.2)⁻¹ * G (Function.update x 0 u, ζ))) := by
    funext r
    rw [Function.uncurry, hUpdateConst' r.2]
    rfl
  have hHauxOn : AnalyticOnNhd ℂ Haux Daux := fin2Hartogs hDauxOpen hHauxSep
  have hHauxAt : AnalyticAt ℂ Haux (φ q) := hHauxOn (φ q) hφMem
  -- Pull the auxiliary `Fin 2` germ back to the weighted torus surface once the callback exists.
  rw [← hKernel]
  exact hHauxAt.comp hφAt

/-- Helper for Theorem IV.5-extra-2: the single remaining product-domain frontier is a noncircular
Hartogs closeout on `((Fin (m + 1) → ℂ) × ℂ)`. All three former consumer `sorry`s factor through
this callback, so keeping it explicit isolates the actual missing premise. -/
lemma normalizedProductCauchySeries_analyticAt_center_direct_local
    {m : ℕ}
    (ih : ∀ {D' : Set (Fin (m + 1) → ℂ)} {f' : (Fin (m + 1) → ℂ) → ℂ},
      IsOpen D' →
      (∀ z ∈ D', ∀ i : Fin (m + 1), AnalyticAt ℂ (fun w ↦ f' (Function.update z i w)) (z i)) →
      AnalyticOnNhd ℂ f' D')
    {D : Set ((Fin (m + 1) → ℂ) × ℂ)} {G : ((Fin (m + 1) → ℂ) × ℂ) → ℂ}
    {p : (Fin (m + 1) → ℂ) × ℂ} {ρ : ℝ}
    (hD : IsOpen D)
    (hρpos : 0 < ρ)
    (hcyl : Metric.ball p.1 (ρ / 2) ×ˢ Metric.closedBall p.2 (ρ / 2) ⊆ D)
    (hsep : ∀ q ∈ D,
      AnalyticAt ℂ (fun x : Fin (m + 1) → ℂ ↦ G (x, q.2)) q.1 ∧
        AnalyticAt ℂ (fun u : ℂ ↦ G (q.1, u)) q.2) :
    AnalyticAt ℂ
      (fun q : (Fin (m + 1) → ℂ) × ℂ ↦
        ∑' n : ℕ,
          (cauchyPowerSeries (fun ζ ↦ G (q.1, ζ)) p.2 (ρ / 2)).coeff n * (q.2 - p.2) ^ n)
      p := by
  -- Route correction: the theorem body below is already reduced to this centered-series germ, so
  -- keep the remaining blocker on the exact normalized `tsum` surface rather than inside the
  -- product Hartogs callback itself.
  -- TODO: `prodBoundaryIntegrand_analyticOnNhd_commonBall_local` now sits earlier in the file, so
  -- the next noncircular step can build the coefficient-row analytic package before attacking the
  -- remaining compact-torus uniformization and centered formal-series owner.
  sorry

/-- Helper for Theorem IV.5-extra-2: the single remaining product-domain frontier is a noncircular
Hartogs closeout on `((Fin (m + 1) → ℂ) × ℂ)`. All three former consumer `sorry`s factor through
this callback, so keeping it explicit isolates the actual missing premise. -/
lemma separatelyHolomorphicProd_analyticOnNhd_base_local
    {m : ℕ}
    (ih : ∀ {D' : Set (Fin (m + 1) → ℂ)} {f' : (Fin (m + 1) → ℂ) → ℂ},
      IsOpen D' →
      (∀ z ∈ D', ∀ i : Fin (m + 1), AnalyticAt ℂ (fun w ↦ f' (Function.update z i w)) (z i)) →
      AnalyticOnNhd ℂ f' D')
    {D : Set ((Fin (m + 1) → ℂ) × ℂ)} {G : ((Fin (m + 1) → ℂ) × ℂ) → ℂ}
    (hD : IsOpen D)
    (hsep : ∀ p ∈ D,
      AnalyticAt ℂ (fun w : Fin (m + 1) → ℂ ↦ G (w, p.2)) p.1 ∧
        AnalyticAt ℂ (fun w ↦ G (p.1, w)) p.2) :
    AnalyticOnNhd ℂ G D := by
  intro p hp
  obtain ⟨ρ, hρpos, hcyl⟩ := exists_productCylinder_subset_of_isOpen_local hD hp
  let H : ((Fin (m + 1) → ℂ) × ℂ) → ℂ := fun q ↦
    ∑' n : ℕ,
      (cauchyPowerSeries (fun ζ ↦ G (q.1, ζ)) p.2 (ρ / 2)).coeff n * (q.2 - p.2) ^ n
  have hHEqG :
      Set.EqOn H G (Metric.ball p (ρ / 8)) := by
    -- The normalized local Cauchy series already agrees with `G` on the smaller common ball.
    simpa [H] using
      normalizedProductCauchySeries_eqOn_smallBall_local
        (m := m) (D := D) (G := G) (p := p) (ρ := ρ) hρpos hsep hcyl
  have hHAt : AnalyticAt ℂ H p := by
    -- Delegate the centered normalized-series germ to the dedicated theorem-local helper so the
    -- base Hartogs callback only retains the final `AnalyticAt.congr` transfer.
    simpa [H] using
      normalizedProductCauchySeries_analyticAt_center_direct_local
        (m := m) ih (D := D) (G := G) (p := p) (ρ := ρ) hD hρpos hcyl hsep
  have hEventually :
      H =ᶠ[nhds p] G := by
    filter_upwards [Metric.ball_mem_nhds p (show 0 < ρ / 8 by positivity)] with q hq
    exact hHEqG hq
  -- Once the normalized series is analytic at the center, the small-ball identity transfers the
  -- germ back to `G` by `AnalyticAt.congr`.
  exact hHAt.congr hEventually

/-- Helper for Theorem IV.5-extra-2: the remaining coefficient-row frontier is the joint
continuity of the weighted `(ζ,u)` family on the outer torus and inner closed disc. The fixed-`u`
continuity is already isolated above, so only the Hartogs-style separate-to-joint upgrade remains.
-/
lemma weightedBoundarySliceJointContinuousOnTorus_local
    {m : ℕ}
    (ih : ∀ {D' : Set (Fin (m + 1) → ℂ)} {f' : (Fin (m + 1) → ℂ) → ℂ},
      IsOpen D' →
      (∀ z ∈ D', ∀ i : Fin (m + 1), AnalyticAt ℂ (fun w ↦ f' (Function.update z i w)) (z i)) →
      AnalyticOnNhd ℂ f' D')
    {D : Set ((Fin (m + 1) → ℂ) × ℂ)} {G : ((Fin (m + 1) → ℂ) × ℂ) → ℂ}
    {p : (Fin (m + 1) → ℂ) × ℂ} {ρ : ℝ}
    (hD : IsOpen D)
    (hρpos : 0 < ρ)
    (hcyl : Metric.ball p.1 (ρ / 2) ×ˢ Metric.closedBall p.2 (ρ / 2) ⊆ D)
    (hsep : ∀ q ∈ D,
      AnalyticAt ℂ (fun x : Fin (m + 1) → ℂ ↦ G (x, q.2)) q.1 ∧
        AnalyticAt ℂ (fun u : ℂ ↦ G (q.1, u)) q.2)
    (hBoundaryCommonBall :
      ∀ ζ ∈ Metric.sphere p.2 (ρ / 2),
        AnalyticOnNhd ℂ
          (fun q : (Fin (m + 1) → ℂ) × ℂ ↦ (ζ - q.2)⁻¹ * G (q.1, ζ))
          (Metric.ball p (ρ / 8)))
    {n : ℕ} {x : Fin (m + 1) → ℂ} (hx : x ∈ Metric.ball p.1 (ρ / 8))
    {i : Fin (m + 1)} {R : NNReal} (hRpos : 0 < R)
    (hInsertMaps :
      Set.MapsTo (fun u : ℂ ↦ (Function.update x i u, p.2))
        (Metric.closedBall (x i) (R : ℝ)) (Metric.ball p (ρ / 8))) :
    ContinuousOn
      (Function.uncurry fun ζ u ↦
        ((ζ - p.2)⁻¹) ^ n * ((ζ - p.2)⁻¹ * G (Function.update x i u, ζ)))
      (Metric.sphere p.2 (ρ / 2) ×ˢ Metric.closedBall (x i) (R : ℝ)) := by
  -- Route correction: the transport-free proof should port the auxiliary Hartogs argument from
  -- `HigherDimensionalHartogs.lean` to the direct `G` notation. The fixed-`u` continuity side is
  -- already isolated by `weightedBoundarySlice_continuousOn_sphere_local`; the remaining work is
  -- the pole-free separate-to-joint analyticity upgrade on the auxiliary domain.
  refine continuousOn_of_forall_analyticAt ?_
  intro q hq
  rcases hq with ⟨hqSphere, hqClosed⟩
  have hqInsert : (Function.update x i q.2, p.2) ∈ Metric.ball p (ρ / 8) :=
    hInsertMaps hqClosed
  have hqBlock : Function.update x i q.2 ∈ Metric.ball p.1 (ρ / 8) := by
    rw [Metric.mem_ball, Prod.dist_eq] at hqInsert
    exact (max_lt_iff.mp hqInsert).1
  have hsmall_lt : ρ / 8 < ρ / 2 := by
    linarith
  have hqD : (Function.update x i q.2, q.1) ∈ D := by
    exact hcyl ⟨Metric.ball_subset_ball (le_of_lt hsmall_lt) hqBlock,
      Metric.sphere_subset_closedBall hqSphere⟩
  have hqNe : q.1 ≠ p.2 := by
    intro hEq
    have hdist : dist q.1 p.2 = ρ / 2 := by
      simpa [Metric.mem_sphere, dist_eq_norm] using hqSphere
    have : dist q.1 p.2 = 0 := by
      simp [hEq]
    linarith
  have hBlockSliceAt :
      AnalyticAt ℂ
        (fun u ↦
          ((q.1 - p.2)⁻¹) ^ n * ((q.1 - p.2)⁻¹ * G (Function.update x i u, q.1)))
        q.2 := by
    -- Freeze the boundary value `q.1` and compose the common-ball germ with the insertion map.
    have hBoundaryAt :
        AnalyticAt ℂ
          (fun r : (Fin (m + 1) → ℂ) × ℂ ↦ (q.1 - r.2)⁻¹ * G (r.1, q.1))
          (Function.update x i q.2, p.2) := by
      exact hBoundaryCommonBall q.1 hqSphere _ hqInsert
    have hInsertAt :
        AnalyticAt ℂ (fun u : ℂ ↦ (Function.update x i u, p.2)) q.2 := by
      simpa [Function.update] using
        (analyticAt_update_coordinate_prod_const (Function.update x i q.2) i p.2)
    have hInsertCenter :
        (fun u : ℂ ↦ (Function.update x i u, p.2)) q.2 = (Function.update x i q.2, p.2) := by
      simp
    have hSliceAt :
        AnalyticAt ℂ (fun u ↦ (q.1 - p.2)⁻¹ * G (Function.update x i u, q.1)) q.2 := by
      simpa using
        hBoundaryAt.comp_of_eq (f := fun u : ℂ ↦ (Function.update x i u, p.2))
          (x := q.2) hInsertAt hInsertCenter
    simpa [mul_assoc] using (analyticAt_const.mul hSliceAt)
  have hLastSliceAt :
      AnalyticAt ℂ
        (fun ζ ↦
          ((ζ - p.2)⁻¹) ^ n * ((ζ - p.2)⁻¹ * G (Function.update x i q.2, ζ)))
        q.1 := by
    -- Freeze the block coordinate and keep the pole-free last-variable germ explicit.
    have hGLast :
        AnalyticAt ℂ (fun ζ : ℂ ↦ G (Function.update x i q.2, ζ)) q.1 := (hsep _ hqD).2
    have hKernel :
        AnalyticAt ℂ (fun ζ : ℂ ↦ (ζ - p.2)⁻¹) q.1 := by
      exact (analyticAt_id.sub analyticAt_const).inv (by simpa using sub_ne_zero.mpr hqNe)
    exact (hKernel.pow n).mul (hKernel.mul hGLast)
  by_cases hm : m = 0
  · -- TODO: the remaining base case is the genuine `Fin 2` Hartogs owner on the auxiliary
    -- domain `Daux`. The auxiliary domain openness and separate analyticity are now isolated
    -- below, and the base case is reduced to the single product-Hartogs frontier theorem above.
    subst hm
    fin_cases i
    have ih1 :
        ∀ {D' : Set (Fin 1 → ℂ)} {f' : (Fin 1 → ℂ) → ℂ},
          IsOpen D' →
          (∀ z ∈ D', ∀ i : Fin 1, AnalyticAt ℂ (fun w ↦ f' (Function.update z i w)) (z i)) →
          AnalyticOnNhd ℂ f' D' := by
      intro D' f' _ hsep'
      -- In one complex variable the unique coordinate slice is the whole function.
      exact separatelyHolomorphicSingleton_analyticOnNhd hsep'
    have hFin2 :
        ∀ {D2 : Set (Fin 2 → ℂ)} {F : (Fin 2 → ℂ) → ℂ},
          IsOpen D2 →
          (∀ z ∈ D2, ∀ k : Fin 2, AnalyticAt ℂ (fun w ↦ F (Function.update z k w)) (z k)) →
          AnalyticOnNhd ℂ F D2 := by
      intro D2 F hD2 hsep2
      -- The `Fin 2` transport package only needs the `Fin 1 × ℂ` product Hartogs callback.
      simpa using
        separatelyHolomorphicFin2_analyticOnNhd_ofProdHartogs_local
          (prodHartogs := fun hDprod hsepProd ↦
            separatelyHolomorphicProd_analyticOnNhd_base_local
              (m := 0) ih1 hDprod hsepProd)
          hD2 hsep2
    -- Consume the dedicated base-case pullback wrapper once the `Fin 2` callback is available.
    exact
      weightedBoundarySliceAnalyticAt_base_ofFin2Hartogs_local
        (fin2Hartogs := hFin2) (D := D) (G := G) (p := p) (n := n) (x := x) (q := q)
        hD hsep hqD hqNe
  · obtain ⟨m', rfl⟩ := Nat.exists_eq_succ_of_ne_zero hm
    let i0 : Fin (m' + 2) := i
    let j : Fin (m' + 2) := Fin.succAbove i0 (Fin.last m')
    let Daux : Set (Fin (m' + 2) → ℂ) :=
      {y | (Function.update x i0 (y i0), y j) ∈ D ∧ y j ≠ p.2}
    let Haux : (Fin (m' + 2) → ℂ) → ℂ := fun y ↦
      ((y j - p.2)⁻¹) ^ n * ((y j - p.2)⁻¹ * G (Function.update x i0 (y i0), y j))
    let pack : ℂ × ℂ → Fin (m' + 2) → ℂ := fun r ↦
      Function.update (Function.update x j r.1) i0 r.2
    have hij : i0 ≠ j := Fin.ne_succAbove i0 (Fin.last m')
    have hDauxOpen : IsOpen Daux := by
      -- The auxiliary domain keeps exactly the original product-domain membership and the
      -- pole-avoidance condition visible to the induction hypothesis.
      have hblockCont :
          Continuous (fun y : Fin (m' + 2) → ℂ ↦ Function.update x i0 (y i0)) := by
        refine continuous_pi fun k ↦ ?_
        by_cases hk : k = i0
        · simpa [Function.update, hk] using
            (continuous_apply i0 : Continuous fun y : Fin (m' + 2) → ℂ ↦ y i0)
        · simpa [Function.update, hk] using
            (continuous_const : Continuous fun _ : Fin (m' + 2) → ℂ ↦ x k)
      have hpairCont :
          Continuous (fun y : Fin (m' + 2) → ℂ ↦ (Function.update x i0 (y i0), y j)) := by
        exact hblockCont.prodMk (continuous_apply j)
      have hmemOpen :
          IsOpen {y : Fin (m' + 2) → ℂ | (Function.update x i0 (y i0), y j) ∈ D} :=
        hD.preimage hpairCont
      have hneOpen : IsOpen {y : Fin (m' + 2) → ℂ | y j ≠ p.2} := by
        change IsOpen ((fun y : Fin (m' + 2) → ℂ ↦ y j) ⁻¹' ({p.2}ᶜ))
        exact (isClosed_singleton.preimage (continuous_apply j)).isOpen_compl
      simpa [Daux, Set.setOf_and] using hmemOpen.inter hneOpen
    have hHauxOn : AnalyticOnNhd ℂ Haux Daux := by
      refine ih hDauxOpen ?_
      intro y hy k
      rcases hy with ⟨hyD, hyNe⟩
      by_cases hk_i : k = i0
      · subst hk_i
        have hji : j ≠ i0 := hij.symm
        have hSliceEq :
            (fun w : ℂ ↦ Haux (Function.update y i0 w)) =
              (fun w ↦
                ((y j - p.2)⁻¹) ^ n *
                  ((y j - p.2)⁻¹ * G (Function.update x i0 w, y j))) := by
          funext w
          simp [Haux, Function.update, hij, hji]
        rw [hSliceEq]
        have hBlockAt :
            AnalyticAt ℂ (fun z : Fin (m' + 2) → ℂ ↦ G (z, y j))
              (Function.update x i0 (y i0)) := (hsep _ hyD).1
        have hUpdateAt :
            AnalyticAt ℂ (fun w : ℂ ↦ Function.update x i0 w) (y i0) := by
          simpa [Function.update] using
            (analyticAt_update_coordinate (Function.update x i0 (y i0)) i0)
        have hUpdateCenter :
            (fun w : ℂ ↦ Function.update x i0 w) (y i0) = Function.update x i0 (y i0) := by
          simp
        have hSliceAt :
            AnalyticAt ℂ (fun w ↦ G (Function.update x i0 w, y j)) (y i0) := by
          simpa using
            hBlockAt.comp_of_eq (f := fun w : ℂ ↦ Function.update x i0 w) (x := y i0)
              hUpdateAt hUpdateCenter
        simpa [mul_assoc] using (analyticAt_const.mul (analyticAt_const.mul hSliceAt))
      by_cases hk_j : k = j
      · subst hk_j
        have hji : j ≠ i0 := hij.symm
        have hSliceEq :
            (fun w : ℂ ↦ Haux (Function.update y j w)) =
              (fun w ↦
                ((w - p.2)⁻¹) ^ n * ((w - p.2)⁻¹ * G (Function.update x i0 (y i0), w))) := by
          funext w
          simp [Haux, Function.update, hij, hji]
        rw [hSliceEq]
        have hGLast :
            AnalyticAt ℂ (fun w : ℂ ↦ G (Function.update x i0 (y i0), w)) (y j) := (hsep _ hyD).2
        have hKernel :
            AnalyticAt ℂ (fun w : ℂ ↦ (w - p.2)⁻¹) (y j) := by
          exact (analyticAt_id.sub analyticAt_const).inv (by simpa using sub_ne_zero.mpr hyNe)
        exact (hKernel.pow n).mul (hKernel.mul hGLast)
      · -- All remaining coordinates are dummy parameters of `Haux`, so those slices are constant.
        have hik : i0 ≠ k := by
          intro hEq
          exact hk_i hEq.symm
        have hjk : j ≠ k := by
          intro hEq
          exact hk_j hEq.symm
        have hSliceEq :
            (fun w : ℂ ↦ Haux (Function.update y k w)) =
              (fun _ : ℂ ↦
                ((y j - p.2)⁻¹) ^ n *
                  ((y j - p.2)⁻¹ * G (Function.update x i0 (y i0), y j))) := by
          funext w
          simp [Haux, Function.update, hik, hjk]
        rw [hSliceEq]
        exact analyticAt_const
    have hPackMem : pack q ∈ Daux := by
      have hji : j ≠ i0 := hij.symm
      have hpack_i : pack q i0 = q.2 := by
        simp [pack, Function.update, hij, hji]
      have hpack_j : pack q j = q.1 := by
        simp [pack, Function.update, hij, hji]
      refine ⟨?_, ?_⟩
      · rw [hpack_i, hpack_j]
        exact hqD
      · rw [hpack_j]
        exact hqNe
    have hPackAnalytic : AnalyticAt ℂ pack q := analyticAt_update_twoCoordinates hij q
    have hPackKernel :
        (fun r : ℂ × ℂ ↦ Haux (pack r)) =
          Function.uncurry
            (fun ζ u ↦ ((ζ - p.2)⁻¹) ^ n * ((ζ - p.2)⁻¹ * G (Function.update x i u, ζ))) := by
      funext r
      have hji : j ≠ i0 := hij.symm
      simp [Function.uncurry, Haux, pack, Function.update, hij, hji, i0]
    have hHauxAt : AnalyticAt ℂ Haux (pack q) := hHauxOn (pack q) hPackMem
    rw [← hPackKernel]
    exact hHauxAt.comp hPackAnalytic

/-- Helper for Theorem IV.5-extra-2: each frozen boundary integrand
`q ↦ (ζ - q.2)⁻¹ * G (q.1, ζ)` is already analytic on the common small ball. -/
lemma prodBoundaryIntegrand_analyticOnNhd_commonBall_local
    {m : ℕ}
    {D : Set ((Fin (m + 1) → ℂ) × ℂ)} {G : ((Fin (m + 1) → ℂ) × ℂ) → ℂ}
    {p : (Fin (m + 1) → ℂ) × ℂ} {ρ : ℝ}
    (hρpos : 0 < ρ)
    (hsep : ∀ q ∈ D,
      AnalyticAt ℂ (fun x : Fin (m + 1) → ℂ ↦ G (x, q.2)) q.1 ∧
        AnalyticAt ℂ (fun u : ℂ ↦ G (q.1, u)) q.2)
    (hcyl : Metric.ball p.1 (ρ / 2) ×ˢ Metric.closedBall p.2 (ρ / 2) ⊆ D)
    {ζ : ℂ} (hζ : ζ ∈ Metric.sphere p.2 (ρ / 2)) :
    AnalyticOnNhd ℂ
      (fun q : (Fin (m + 1) → ℂ) × ℂ ↦ (ζ - q.2)⁻¹ * G (q.1, ζ))
      (Metric.ball p (ρ / 8)) := by
  have hBoundary :
      AnalyticOnNhd ℂ
        (fun x : Fin (m + 1) → ℂ ↦ G (x, ζ))
        (Metric.ball p.1 (ρ / 2)) := by
    intro x hx
    -- Freeze the boundary value `ζ` and read off the block analyticity directly from `hsep`.
    exact (hsep (x, ζ) (hcyl ⟨hx, Metric.sphere_subset_closedBall hζ⟩)).1
  have hg :
      AnalyticOnNhd ℂ
        (fun q : (Fin (m + 1) → ℂ) × ℂ ↦ G (q.1, ζ))
        (Metric.ball p (ρ / 8)) := by
    -- Pull the frozen boundary slice back along the first projection on the common small ball.
    refine hBoundary.comp (analyticOnNhd_fst (𝕜 := ℂ)
      (E := Fin (m + 1) → ℂ) (F := ℂ) (t := Metric.ball p (ρ / 8))) ?_
    intro q hq
    have hqProd : max (dist q.1 p.1) (dist q.2 p.2) < ρ / 8 := by
      simpa [Metric.mem_ball, Prod.dist_eq] using hq
    have hqBlock : dist q.1 p.1 < ρ / 8 := (max_lt_iff.mp hqProd).1
    have heighth_lt_half : ρ / 8 < ρ / 2 := by
      linarith
    simpa [Metric.mem_ball] using lt_trans hqBlock heighth_lt_half
  have hkernelSub :
      AnalyticOnNhd ℂ
        (fun q : (Fin (m + 1) → ℂ) × ℂ ↦ ζ - q.2)
        (Metric.ball p (ρ / 8)) := by
    -- The denominator is the affine last-coordinate germ on the same common small ball.
    exact
      analyticOnNhd_const.sub
        (analyticOnNhd_snd (𝕜 := ℂ)
          (E := Fin (m + 1) → ℂ) (F := ℂ) (t := Metric.ball p (ρ / 8)))
  have hkernel :
      AnalyticOnNhd ℂ
        (fun q : (Fin (m + 1) → ℂ) × ℂ ↦ (ζ - q.2)⁻¹)
        (Metric.ball p (ρ / 8)) := by
    -- The boundary circle stays away from the last coordinate throughout the smaller common ball.
    refine hkernelSub.inv ?_
    intro q hq hzero
    have hqProd : max (dist q.1 p.1) (dist q.2 p.2) < ρ / 8 := by
      simpa [Metric.mem_ball, Prod.dist_eq] using hq
    have hqLast : dist q.2 p.2 < ρ / 8 := (max_lt_iff.mp hqProd).2
    have hζdist : dist ζ p.2 = ρ / 2 := by
      simpa [Metric.mem_sphere, dist_eq_norm] using hζ
    have hEq : ζ = q.2 := sub_eq_zero.mp hzero
    have : ρ / 2 < ρ / 8 := by
      calc
        ρ / 2 = dist ζ p.2 := hζdist.symm
        _ = dist q.2 p.2 := by rw [hEq]
        _ < ρ / 8 := hqLast
    linarith [hρpos]
  -- Multiply the nonvanishing boundary kernel by the frozen boundary slice on the same small ball.
  exact hkernel.mul hg

/-- Helper for Theorem IV.5-extra-2: once the weighted torus-continuity input is isolated, each
centered last-variable Cauchy coefficient row is analytic on the inner block ball. -/
lemma productCauchyCoeffAnalyticOnNhd_local
    {m : ℕ}
    (ih : ∀ {D' : Set (Fin (m + 1) → ℂ)} {f' : (Fin (m + 1) → ℂ) → ℂ},
      IsOpen D' →
      (∀ z ∈ D', ∀ i : Fin (m + 1), AnalyticAt ℂ (fun w ↦ f' (Function.update z i w)) (z i)) →
      AnalyticOnNhd ℂ f' D')
    {D : Set ((Fin (m + 1) → ℂ) × ℂ)} {G : ((Fin (m + 1) → ℂ) × ℂ) → ℂ}
    {p : (Fin (m + 1) → ℂ) × ℂ} {ρ : ℝ}
    (hD : IsOpen D)
    (hρpos : 0 < ρ)
    (hcyl : Metric.ball p.1 (ρ / 2) ×ˢ Metric.closedBall p.2 (ρ / 2) ⊆ D)
    (hsep : ∀ q ∈ D,
      AnalyticAt ℂ (fun x : Fin (m + 1) → ℂ ↦ G (x, q.2)) q.1 ∧
        AnalyticAt ℂ (fun u : ℂ ↦ G (q.1, u)) q.2)
    (hBoundaryCommonBall :
      ∀ ζ ∈ Metric.sphere p.2 (ρ / 2),
        AnalyticOnNhd ℂ
          (fun q : (Fin (m + 1) → ℂ) × ℂ ↦ (ζ - q.2)⁻¹ * G (q.1, ζ))
          (Metric.ball p (ρ / 8))) :
    let w0 : ℂ := p.2
    let r0 : ℝ := ρ / 8
    let A : ℕ → (Fin (m + 1) → ℂ) → ℂ := fun n x ↦
      (cauchyPowerSeries (fun ζ ↦ G (x, ζ)) w0 (ρ / 2)).coeff n
    ∀ n : ℕ, AnalyticOnNhd ℂ (A n) (Metric.ball p.1 r0) := by
  let w0 : ℂ := p.2
  let r0 : ℝ := ρ / 8
  let A : ℕ → (Fin (m + 1) → ℂ) → ℂ := fun n x ↦
    (cauchyPowerSeries (fun ζ ↦ G (x, ζ)) w0 (ρ / 2)).coeff n
  -- Keep the proof on the explicit coefficient-row surface, then fold it back into the frozen
  -- local notation `w0`, `r0`, and `A`.
  simpa [w0, r0, A] using
    (show
      ∀ n : ℕ,
        AnalyticOnNhd ℂ
          (fun x : Fin (m + 1) → ℂ ↦
            (cauchyPowerSeries (fun ζ ↦ G (x, ζ)) p.2 (ρ / 2)).coeff n)
          (Metric.ball p.1 (ρ / 8)) from by
      intro n
      refine ih Metric.isOpen_ball ?_
      intro x hx i
      rcases
          weightedBoundarySlice_hasFPowerSeriesOnBall_of_commonBall
            (g := G) (center := p) (r0 := r0) (outerR := ρ / 2)
            hBoundaryCommonBall n x hx i with
        ⟨R, hRpos, hInsertMaps, hBoundarySlicePackage⟩
      have hRrealPos : 0 < (R : ℝ) := by
        exact_mod_cast hRpos
      let b : ℕ → ℂ → ℂ := fun q ζ ↦
        (cauchyPowerSeries
          (fun u ↦
            ((ζ - w0)⁻¹) ^ n * ((ζ - w0)⁻¹ * G (Function.update x i u, ζ)))
          (x i) R).coeff q
      have hBoundarySeriesOnBall :
          ∀ ζ ∈ Metric.sphere w0 (ρ / 2),
            HasFPowerSeriesOnBall
              (fun u ↦
                ((ζ - w0)⁻¹) ^ n * ((ζ - w0)⁻¹ * G (Function.update x i u, ζ)))
              (cauchyPowerSeries
                (fun u ↦
                  ((ζ - w0)⁻¹) ^ n * ((ζ - w0)⁻¹ * G (Function.update x i u, ζ)))
                (x i) R)
              (x i) R := by
        intro ζ hζ
        exact (hBoundarySlicePackage ζ hζ).1
      have hCoeffPackage :
          ∃ M : ℝ, 0 ≤ M ∧
            ∀ q : ℕ,
              ContinuousOn (b q) (Metric.sphere w0 (ρ / 2)) ∧
                ∀ ζ ∈ Metric.sphere w0 (ρ / 2), ‖b q ζ‖ ≤ M / (R : ℝ) ^ q := by
        let outerR : NNReal := ⟨ρ / 2, by positivity⟩
        have hJointTorus :
            ContinuousOn
              (Function.uncurry fun ζ u ↦
                ((ζ - w0)⁻¹) ^ n * ((ζ - w0)⁻¹ * G (Function.update x i u, ζ)))
              (Metric.sphere w0 (outerR : ℝ) ×ˢ Metric.closedBall (x i) (R : ℝ)) := by
          -- The remaining joint-torus continuity frontier is isolated in one dedicated helper.
          exact
            weightedBoundarySliceJointContinuousOnTorus_local
              (m := m) ih (D := D) (G := G) (p := p) (ρ := ρ) hD hρpos hcyl hsep
              hBoundaryCommonBall hx hRpos hInsertMaps
        simpa [b, outerR] using
          weightedBoundarySliceCoeffRow_package_of_jointTorusContinuous_local
            (u0 := x i) (c := w0) (innerR := R) (outerR := outerR) (n := n)
            (g := fun u ζ ↦ G (Function.update x i u, ζ)) hRpos hJointTorus
      rcases hCoeffPackage with ⟨M, hMnonneg, hrowB⟩
      have hcontB (q : ℕ) : ContinuousOn (b q) (Metric.sphere w0 (ρ / 2)) := (hrowB q).1
      have hboundB (q : ℕ) (ζ : ℂ) (hζ : ζ ∈ Metric.sphere w0 (ρ / 2)) :
          ‖b q ζ‖ ≤ M / (R : ℝ) ^ q := (hrowB q).2 ζ hζ
      have hIntegralAt :
          AnalyticAt ℂ
            (fun u ↦
              ((2 * Real.pi * Complex.I : ℂ)⁻¹ •
                ∮ ζ in C(w0, ρ / 2),
                  ((ζ - w0)⁻¹) ^ n * ((ζ - w0)⁻¹ * G (Function.update x i u, ζ))))
            (x i) := by
        exact
          analyticAt_centeredCircleIntegral_of_hasFPowerSeriesOnBall_coeffRow_local
            (u0 := x i) (c := w0) (outerR := ρ / 2) (innerR := R) (M := M)
            (by positivity) hRrealPos hMnonneg
            (F := fun ζ u ↦
              ((ζ - w0)⁻¹) ^ n * ((ζ - w0)⁻¹ * G (Function.update x i u, ζ)))
            (hseries := hBoundarySeriesOnBall) hcontB hboundB
      have hEqSlice :
          (fun u ↦ (cauchyPowerSeries (fun ζ ↦ G (Function.update x i u, ζ)) p.2 (ρ / 2)).coeff n) =
            (fun u ↦
              ((2 * Real.pi * Complex.I : ℂ)⁻¹ •
                ∮ ζ in C(w0, ρ / 2),
                  ((ζ - w0)⁻¹) ^ n * ((ζ - w0)⁻¹ * G (Function.update x i u, ζ)))) := by
        funext u
        simpa [w0] using
          productCauchyCoeffSlice_eq_centeredIntegral_local
            (G := G) (p := p) (ρ := ρ) n x i u
      -- Rewrite the coefficient slice into the centered boundary integral spelling closed above.
      simpa [hEqSlice] using hIntegralAt)

/-- Helper for Theorem IV.5-extra-2: every finite centered partial sum of the normalized product
Cauchy series is analytic on the product neighborhood determined by the coefficient-domain ball and
the last-variable ball. -/
lemma normalizedProductCauchySeries_partialSums_analyticOnNhd_local
    {m : ℕ}
    {A : ℕ → (Fin (m + 1) → ℂ) → ℂ} {x0 : Fin (m + 1) → ℂ} {u0 : ℂ}
    {r R : ℝ}
    (hCoeffOn : ∀ n : ℕ, AnalyticOnNhd ℂ (A n) (Metric.ball x0 r)) :
    ∀ N : ℕ,
      AnalyticOnNhd ℂ
        (∑ n ∈ Finset.range N, fun q : (Fin (m + 1) → ℂ) × ℂ ↦ A n q.1 * (q.2 - u0) ^ n)
        (Metric.ball x0 r ×ˢ Metric.ball u0 R) := by
  intro N
  -- Each finite summand is the canonical coefficient-times-centered-monomial germ on the same
  -- product neighborhood, so the whole partial sum stays analytic by finite summation.
  simpa [Finset.sum_apply] using
    (Finset.analyticOnNhd_sum
      (Finset.range N) fun n hn ↦
        analyticOnNhd_parametricPowerSeriesTerm_local (hCoeffOn n))

/-- Helper for Theorem IV.5-extra-2: a uniform geometric coefficient bound on the smaller closed
block ball turns every normalized product-series term into the standard `C * (1 / 2)^n` majorant
on the corresponding block-disc product neighborhood. -/
lemma normalizedProductCauchySeries_termBound_local
    {m : ℕ}
    {A : ℕ → (Fin (m + 1) → ℂ) → ℂ} {x0 : Fin (m + 1) → ℂ} {u0 : ℂ}
    {r R C : ℝ}
    (hR : 0 < R)
    (hCoeffBound : ∀ x ∈ Metric.closedBall x0 (r / 2), ∀ n : ℕ, ‖A n x‖ ≤ C / R ^ n) :
    ∀ n : ℕ, ∀ q ∈ Metric.closedBall x0 (r / 2) ×ˢ Metric.ball u0 (R / 2),
      ‖A n q.1 * (q.2 - u0) ^ n‖ ≤ C * (1 / 2 : ℝ) ^ n := by
  intro n q hq
  have hCoeffBudget : ‖A n q.1‖ ≤ C / R ^ n := hCoeffBound q.1 hq.1 n
  have hPowerBudget :
      ‖(q.2 - u0) ^ n‖ ≤ R ^ n * (1 / 2 : ℝ) ^ n :=
    norm_sub_pow_le_halfRadius_geometric_local hR n hq.2
  have hCoeffBudgetNonneg : 0 ≤ C / R ^ n := by
    exact le_trans (norm_nonneg _) hCoeffBudget
  have hRne : R ≠ 0 := ne_of_gt hR
  -- Separate the coefficient norm from the last-variable power and feed both parts into the
  -- standard half-radius majorant computation once.
  calc
    ‖A n q.1 * (q.2 - u0) ^ n‖ = ‖A n q.1‖ * ‖(q.2 - u0) ^ n‖ := by
      rw [norm_mul]
    _ ≤ (C / R ^ n) * ‖(q.2 - u0) ^ n‖ := by
      exact mul_le_mul_of_nonneg_right hCoeffBudget (norm_nonneg _)
    _ ≤ (C / R ^ n) * (R ^ n * (1 / 2 : ℝ) ^ n) := by
      exact mul_le_mul_of_nonneg_left hPowerBudget hCoeffBudgetNonneg
    _ = C * (1 / 2 : ℝ) ^ n := by
      field_simp [pow_ne_zero n hRne]

/-- Helper for Theorem IV.5-extra-2: points on the small product ball automatically lie in the
closed/open factor neighborhoods used by the coefficient and monomial bounds. -/
lemma centeredProductWorkingBall_mem_local
    {m : ℕ}
    {x0 : Fin (m + 1) → ℂ} {u0 : ℂ} {r R : ℝ}
    {q : (Fin (m + 1) → ℂ) × ℂ}
    (hq : q ∈ Metric.ball (x0, u0) (min (r / 2) (R / 2))) :
    q.1 ∈ Metric.closedBall x0 (r / 2) ∧ q.2 ∈ Metric.ball u0 (R / 2) := by
  have hqdist : dist q (x0, u0) < min (r / 2) (R / 2) := by
    simpa [Metric.mem_ball] using hq
  have hprod : max (dist q.1 x0) (dist q.2 u0) < min (r / 2) (R / 2) := by
    simpa [Prod.dist_eq] using hqdist
  have hx : dist q.1 x0 < min (r / 2) (R / 2) := (max_lt_iff.mp hprod).1
  have hu : dist q.2 u0 < min (r / 2) (R / 2) := (max_lt_iff.mp hprod).2
  constructor
  · -- The first coordinate stays inside the closed half-radius block ball.
    simpa [Metric.mem_closedBall] using le_trans hx.le (min_le_left _ _)
  · -- The second coordinate already lies in the corresponding open half-radius last-variable ball.
    simpa [Metric.mem_ball] using lt_of_lt_of_le hu (min_le_right _ _)

/-- Helper for Theorem IV.5-extra-2: on the common working product ball, the centered parametric
series is already absolutely summable by the uniform geometric term majorant. -/
lemma centeredParametricSeries_summableOnWorkingBall_local
    {m : ℕ}
    {A : ℕ → (Fin (m + 1) → ℂ) → ℂ} {x0 : Fin (m + 1) → ℂ} {u0 : ℂ}
    {r R C : ℝ}
    (hR : 0 < R)
    (hCoeffBound : ∀ x ∈ Metric.closedBall x0 (r / 2), ∀ n : ℕ, ‖A n x‖ ≤ C / R ^ n)
    {q : (Fin (m + 1) → ℂ) × ℂ}
    (hq : q ∈ Metric.ball (x0, u0) (min (r / 2) (R / 2))) :
    Summable (fun n : ℕ ↦ A n q.1 * (q.2 - u0) ^ n) := by
  rcases centeredProductWorkingBall_mem_local hq with
    ⟨hqBlock, hqLast⟩
  have htermBound :
      ∀ n : ℕ, ‖A n q.1 * (q.2 - u0) ^ n‖ ≤ C * (1 / 2 : ℝ) ^ n := by
    intro n
    -- Put the point into the factor neighborhoods once so the standard geometric term bound applies.
    exact
      normalizedProductCauchySeries_termBound_local
        hR hCoeffBound n q ⟨hqBlock, hqLast⟩
  have hmajorant : Summable (fun n : ℕ ↦ C * (1 / 2 : ℝ) ^ n) := by
    -- The geometric half-radius majorant is summable independently of the point in the working ball.
    simpa [mul_assoc] using (summable_geometric_two.mul_left C)
  -- Dominate the target series termwise by the geometric majorant.
  exact hmajorant.of_norm_bounded htermBound

/-- Helper for Theorem IV.5-extra-2: equality with a centered formal multilinear series on a
genuine ball gives the corresponding `HasFPowerSeriesAt` germ at the center. -/
lemma hasFPowerSeriesAtOfEqFormalSeriesOnBall_local
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    {g : E → ℂ} {P : FormalMultilinearSeries ℂ E ℂ} {x0 : E} {r : ℝ}
    (hr : 0 < r)
    (hRadius : ENNReal.ofReal r ≤ P.radius)
    (hEq : Set.EqOn g (fun y ↦ P.sum (y - x0)) (Metric.ball x0 r)) :
    HasFPowerSeriesAt g P x0 := by
  let g0 : E → ℂ := fun z ↦ g (z + x0)
  have hRadiusPos : 0 < P.radius := by
    exact lt_of_lt_of_le (by simpa using ENNReal.ofReal_pos.mpr hr) hRadius
  have hSeriesFull : HasFPowerSeriesOnBall P.sum P 0 P.radius := by
    -- Start from the canonical power-series owner on its whole convergence ball.
    exact P.hasFPowerSeriesOnBall hRadiusPos
  have hSeriesSmall : HasFPowerSeriesOnBall P.sum P 0 (ENNReal.ofReal r) := by
    -- Restrict the canonical owner back to the concrete ball from the equality hypothesis.
    exact hSeriesFull.mono (by simpa using ENNReal.ofReal_pos.mpr hr) hRadius
  have hEqOn :
      Set.EqOn P.sum g0 (Metric.eball (0 : E) (ENNReal.ofReal r)) := by
    intro z hz
    have hzNorm : ‖z‖ < r := by
      have hzenorm : ‖z‖ₑ < ENNReal.ofReal r := (mem_eball_zero_iff).1 hz
      exact (ENNReal.ofReal_lt_ofReal_iff hr).1 (by simpa [ofReal_norm] using hzenorm)
    have hzBall : z + x0 ∈ Metric.ball x0 r := by
      simpa [Metric.mem_ball, dist_eq_norm, sub_eq_add_neg, add_assoc, add_left_comm, add_comm]
        using hzNorm
    -- Rewrite the shifted point back to the centered `P.sum` normal form fixed by `hEq`.
    simpa [g0, sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using (hEq hzBall).symm
  have hSeriesAtZero : HasFPowerSeriesAt g0 P 0 := (hSeriesSmall.congr hEqOn).hasFPowerSeriesAt
  -- Translate the zero-centered germ back to the actual center `x0`.
  simpa [g0, sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using hSeriesAtZero.comp_sub x0

/-- Helper for Theorem IV.5-extra-2: the centered scalar monomial uses the sparse owner whose only
nonzero scalar coefficient sits in degree `n`. -/
lemma centeredPow_hasFPowerSeriesAt_sparse_local
    {u0 : ℂ} (n : ℕ) :
    HasFPowerSeriesAt
      (fun u : ℂ ↦ (u - u0) ^ n)
      (FormalMultilinearSeries.ofScalars ℂ (fun k ↦ if k = n then (1 : ℂ) else 0))
      u0 := by
  have hs :
      Summable (fun k : ℕ ↦ ‖(if k = n then (1 : ℂ) else 0)‖ * ((1 / 2 : ℝ) ^ k)) := by
    -- Dominate the one-point-supported coefficient sequence by the standard geometric series.
    refine Summable.of_nonneg_of_le (fun _ ↦ by positivity) (fun k ↦ ?_) summable_geometric_two
    by_cases hk : k = n <;> simp [hk]
  have hEq :
      Set.EqOn
        (fun u : ℂ ↦ (u - u0) ^ n)
        (fun u : ℂ ↦ ∑' k : ℕ, (if k = n then (1 : ℂ) else 0) * (u - u0) ^ k)
        (Metric.ball u0 (1 / 2)) := by
    intro u _hu
    -- On the working ball, the sparse owner sum collapses to its unique nonzero degree.
    symm
    calc
      ∑' k : ℕ, (if k = n then (1 : ℂ) else 0) * (u - u0) ^ k
          = (if n = n then (1 : ℂ) else 0) * (u - u0) ^ n := by
              exact tsum_eq_single n (fun k hk ↦ by simp [hk])
      _ = (u - u0) ^ n := by simp
  exact
    hasFPowerSeriesAtOfEqTsumOnBall_centered_local
      (by positivity) hs hEq

/-- Helper for Theorem IV.5-extra-2: the sparse centered scalar monomial owner already controls
`u ↦ (u - u0) ^ n` on every concrete positive-radius ball around `u0`. -/
lemma centeredPow_hasFPowerSeriesOnBall_sparse_local
    {u0 : ℂ} {r : ℝ} (hr : 0 < r) (n : ℕ) :
    HasFPowerSeriesOnBall
      (fun u : ℂ ↦ (u - u0) ^ n)
      (FormalMultilinearSeries.ofScalars ℂ (fun k ↦ if k = n then (1 : ℂ) else 0))
      u0
      (ENNReal.ofReal r) := by
  let p : FormalMultilinearSeries ℂ ℂ ℂ :=
    FormalMultilinearSeries.ofScalars ℂ (fun k ↦ if k = n then (1 : ℂ) else 0)
  have hp_eventually_zero : ∀ᶠ k : ℕ in Filter.atTop, p k = 0 := by
    filter_upwards [Filter.eventually_gt_atTop n] with k hk
    simp [p, Nat.ne_of_gt hk]
  have hp_radius : p.radius = ⊤ := p.radius_eq_top_of_eventually_eq_zero hp_eventually_zero
  have hSeriesTop : HasFPowerSeriesOnBall p.sum p 0 p.radius := by
    -- The sparse owner has infinite radius because all sufficiently high coefficients vanish.
    simpa [hp_radius] using p.hasFPowerSeriesOnBall (by simp [hp_radius])
  have hSeriesCentered : HasFPowerSeriesOnBall (fun u : ℂ ↦ p.sum (u - u0)) p u0 p.radius := by
    -- Translate the zero-centered sparse owner back to the actual center `u0`.
    simpa [hp_radius] using hSeriesTop.comp_sub u0
  have hSeriesBall :
      HasFPowerSeriesOnBall (fun u : ℂ ↦ p.sum (u - u0)) p u0 (ENNReal.ofReal r) := by
    -- Restrict the infinite-radius owner to the concrete ball needed later.
    exact hSeriesCentered.mono (by simpa using ENNReal.ofReal_pos.mpr hr) (by simpa [hp_radius])
  have hEqOn :
      Set.EqOn
        (fun u : ℂ ↦ p.sum (u - u0))
        (fun u : ℂ ↦ (u - u0) ^ n)
        (Metric.eball u0 (ENNReal.ofReal r)) := by
    intro u _hu
    -- The sparse owner sum collapses to its unique nonzero degree.
    change FormalMultilinearSeries.ofScalarsSum
        (fun k ↦ if k = n then (1 : ℂ) else 0) (u - u0) = (u - u0) ^ n
    rw [FormalMultilinearSeries.ofScalarsSum_eq_tsum]
    calc
      ∑' k : ℕ, (if k = n then (1 : ℂ) else 0) • (u - u0) ^ k
          = (if n = n then (1 : ℂ) else 0) • (u - u0) ^ n := by
              exact tsum_eq_single n (fun k hk ↦ by simp [hk])
      _ = (u - u0) ^ n := by simp
  -- Transfer the concrete ball equality back onto the sparse owner.
  simpa [p] using hSeriesBall.congr hEqOn

/-- Helper for Theorem IV.5-extra-2: the sparse centered scalar monomial owner has no lower-degree
scalar coefficients. -/
lemma centeredPow_sparse_coeff_eq_zero_of_lt_local
    {n k : ℕ} (hk : k < n) :
    (FormalMultilinearSeries.ofScalars ℂ (fun q ↦ if q = n then (1 : ℂ) else 0)).coeff k = 0 := by
  -- The coefficient computation is now a direct `simp` fact because the sparse owner is
  -- coefficient-transparent.
  simp [FormalMultilinearSeries.coeff_ofScalars, hk.ne]

/-- Helper for Theorem IV.5-extra-2: a common-radius owner for one coefficient row stays on the
same working ball after pulling it back along the first product projection. -/
lemma coefficientRowCompFst_hasFPowerSeriesOnWorkingBall_local
    {m n : ℕ}
    {A : ℕ → (Fin (m + 1) → ℂ) → ℂ} {x0 : Fin (m + 1) → ℂ} {u0 : ℂ} {r : ℝ}
    {P : FormalMultilinearSeries ℂ (Fin (m + 1) → ℂ) ℂ}
    (hr : 0 < r)
    (hP : HasFPowerSeriesOnBall (A n) P x0 (ENNReal.ofReal (r / 2))) :
    HasFPowerSeriesOnBall
      (fun q : (Fin (m + 1) → ℂ) × ℂ ↦ A n q.1)
      (P.compContinuousLinearMap (ContinuousLinearMap.fst ℂ (Fin (m + 1) → ℂ) ℂ))
      (x0, u0)
      (ENNReal.ofReal (r / 2) /
        ‖ContinuousLinearMap.fst ℂ (Fin (m + 1) → ℂ) ℂ‖ₑ) := by
  -- Pull the row owner back along `fst`; the projection has operator norm `1`.
  let u : ((Fin (m + 1) → ℂ) × ℂ) →L[ℂ] (Fin (m + 1) → ℂ) :=
    ContinuousLinearMap.fst ℂ (Fin (m + 1) → ℂ) ℂ
  have hPull :
      HasFPowerSeriesOnBall
        (A n ∘ Prod.fst)
        (P.compContinuousLinearMap u)
        (x0, u0)
        (ENNReal.ofReal (r / 2) / ‖u‖ₑ) := by
    have hP' : HasFPowerSeriesOnBall (A n) P (u (x0, u0)) (ENNReal.ofReal (r / 2)) := by
      simpa [u] using hP
    simpa [u, Function.comp] using (show
      HasFPowerSeriesOnBall ((A n) ∘ u) (P.compContinuousLinearMap u) (x0, u0)
        (ENNReal.ofReal (r / 2) / ‖u‖ₑ) from hP'.compContinuousLinearMap)
  simpa [u] using hPull

/-- Helper for Theorem IV.5-extra-2: the sparse centered scalar monomial owner stays on the common
working product ball after pulling it back along the second projection. -/
lemma centeredPowCompSnd_hasFPowerSeriesOnWorkingBall_local
    {m : ℕ}
    {x0 : Fin (m + 1) → ℂ} {u0 : ℂ} {R : ℝ}
    (hR : 0 < R) (n : ℕ) :
    HasFPowerSeriesOnBall
      (fun q : (Fin (m + 1) → ℂ) × ℂ ↦ (q.2 - u0) ^ n)
      (FormalMultilinearSeries.compContinuousLinearMap
        (FormalMultilinearSeries.ofScalars ℂ (fun k ↦ if k = n then (1 : ℂ) else 0))
        (ContinuousLinearMap.snd ℂ (Fin (m + 1) → ℂ) ℂ))
      (x0, u0)
      (ENNReal.ofReal (R / 2) /
        ‖ContinuousLinearMap.snd ℂ (Fin (m + 1) → ℂ) ℂ‖ₑ) := by
  let p : FormalMultilinearSeries ℂ ℂ ℂ :=
    FormalMultilinearSeries.ofScalars ℂ (fun k ↦ if k = n then (1 : ℂ) else 0)
  have hPow :
      HasFPowerSeriesOnBall
        (fun u : ℂ ↦ (u - u0) ^ n)
        p
        u0
        (ENNReal.ofReal (R / 2)) := by
    -- Build the scalar sparse owner on the concrete half-radius disc first.
    exact centeredPow_hasFPowerSeriesOnBall_sparse_local (by positivity) n
  -- Pull the scalar owner back along `snd`; again the projection has operator norm `1`.
  let u : ((Fin (m + 1) → ℂ) × ℂ) →L[ℂ] ℂ :=
    ContinuousLinearMap.snd ℂ (Fin (m + 1) → ℂ) ℂ
  have hPull :
      HasFPowerSeriesOnBall
        ((fun u : ℂ ↦ (u - u0) ^ n) ∘ Prod.snd)
        (p.compContinuousLinearMap u)
        (x0, u0)
        (ENNReal.ofReal (R / 2) / ‖u‖ₑ) := by
    have hPow' : HasFPowerSeriesOnBall (fun v : ℂ ↦ (v - u0) ^ n) p (u (x0, u0))
        (ENNReal.ofReal (R / 2)) := by
      simpa [u] using hPow
    simpa [u, p, Function.comp] using (show
      HasFPowerSeriesOnBall ((fun v : ℂ ↦ (v - u0) ^ n) ∘ u)
        (p.compContinuousLinearMap u) (x0, u0) (ENNReal.ofReal (R / 2) / ‖u‖ₑ) from
      hPow'.compContinuousLinearMap)
  simpa [u] using hPull

/-- Helper for Theorem IV.5-extra-2: once the pulled-back block-row owner is available on the
half-radius block ball, it also controls the smaller common working product ball. -/
lemma coefficientRowCompFst_hasFPowerSeriesOnCommonWorkingBall_local
    {m n : ℕ}
    {A : ℕ → (Fin (m + 1) → ℂ) → ℂ} {x0 : Fin (m + 1) → ℂ} {u0 : ℂ} {r R : ℝ}
    {P : FormalMultilinearSeries ℂ (Fin (m + 1) → ℂ) ℂ}
    (hr : 0 < r) (hR : 0 < R)
    (hP : HasFPowerSeriesOnBall (A n) P x0 (ENNReal.ofReal (r / 2))) :
    HasFPowerSeriesOnBall
      (fun q : (Fin (m + 1) → ℂ) × ℂ ↦ A n q.1)
      (P.compContinuousLinearMap (ContinuousLinearMap.fst ℂ (Fin (m + 1) → ℂ) ℂ))
      (x0, u0)
      (ENNReal.ofReal (min (r / 2) (R / 2))) := by
  have hBase :
      HasFPowerSeriesOnBall
        (fun q : (Fin (m + 1) → ℂ) × ℂ ↦ A n q.1)
        (P.compContinuousLinearMap (ContinuousLinearMap.fst ℂ (Fin (m + 1) → ℂ) ℂ))
        (x0, u0)
        (ENNReal.ofReal (r / 2) /
          ‖ContinuousLinearMap.fst ℂ (Fin (m + 1) → ℂ) ℂ‖ₑ) :=
    coefficientRowCompFst_hasFPowerSeriesOnWorkingBall_local
      (A := A) (x0 := x0) (u0 := u0) (r := r) (P := P) hr hP
  have hRadiusLe :
      ENNReal.ofReal (min (r / 2) (R / 2)) ≤
        ENNReal.ofReal (r / 2) / ‖ContinuousLinearMap.fst ℂ (Fin (m + 1) → ℂ) ℂ‖ₑ := by
    -- Rewrite the projection norm to `1`, then the common radius is bounded by the block radius.
    have hfstNorm :
        ‖ContinuousLinearMap.fst ℂ (Fin (m + 1) → ℂ) ℂ‖ₑ = 1 := by
      have hfstNormNN :
          ‖ContinuousLinearMap.fst ℂ (Fin (m + 1) → ℂ) ℂ‖₊ = (1 : NNReal) := by
        apply Subtype.ext
        simpa using ContinuousLinearMap.norm_fst ℂ (Fin (m + 1) → ℂ) ℂ
      simpa [enorm_eq_nnnorm] using hfstNormNN
    rw [hfstNorm, div_one]
    exact ENNReal.ofReal_le_ofReal (min_le_left (r / 2) (R / 2))
  -- Restrict the owner to the smaller common working ball used by the centered series.
  exact hBase.mono (by positivity) hRadiusLe

/-- Helper for Theorem IV.5-extra-2: the pulled-back sparse scalar owner likewise restricts to the
same common working product ball. -/
lemma centeredPowCompSnd_hasFPowerSeriesOnCommonWorkingBall_local
    {m : ℕ}
    {x0 : Fin (m + 1) → ℂ} {u0 : ℂ} {r R : ℝ}
    (hr : 0 < r) (hR : 0 < R) (n : ℕ) :
    HasFPowerSeriesOnBall
      (fun q : (Fin (m + 1) → ℂ) × ℂ ↦ (q.2 - u0) ^ n)
      (FormalMultilinearSeries.compContinuousLinearMap
        (FormalMultilinearSeries.ofScalars ℂ (fun k ↦ if k = n then (1 : ℂ) else 0))
        (ContinuousLinearMap.snd ℂ (Fin (m + 1) → ℂ) ℂ))
      (x0, u0)
      (ENNReal.ofReal (min (r / 2) (R / 2))) := by
  have hBase :
      HasFPowerSeriesOnBall
        (fun q : (Fin (m + 1) → ℂ) × ℂ ↦ (q.2 - u0) ^ n)
        (FormalMultilinearSeries.compContinuousLinearMap
          (FormalMultilinearSeries.ofScalars ℂ (fun k ↦ if k = n then (1 : ℂ) else 0))
          (ContinuousLinearMap.snd ℂ (Fin (m + 1) → ℂ) ℂ))
        (x0, u0)
        (ENNReal.ofReal (R / 2) /
          ‖ContinuousLinearMap.snd ℂ (Fin (m + 1) → ℂ) ℂ‖ₑ) :=
    centeredPowCompSnd_hasFPowerSeriesOnWorkingBall_local
      (x0 := x0) (u0 := u0) (R := R) hR n
  have hRadiusLe :
      ENNReal.ofReal (min (r / 2) (R / 2)) ≤
        ENNReal.ofReal (R / 2) / ‖ContinuousLinearMap.snd ℂ (Fin (m + 1) → ℂ) ℂ‖ₑ := by
    -- After normalizing `‖snd‖ = 1`, the common radius is bounded by the last-variable radius.
    have hsndNorm :
        ‖ContinuousLinearMap.snd ℂ (Fin (m + 1) → ℂ) ℂ‖ₑ = 1 := by
      have hsndNormNN :
          ‖ContinuousLinearMap.snd ℂ (Fin (m + 1) → ℂ) ℂ‖₊ = (1 : NNReal) := by
        apply Subtype.ext
        simpa using ContinuousLinearMap.norm_snd ℂ (Fin (m + 1) → ℂ) ℂ
      simpa [enorm_eq_nnnorm] using hsndNormNN
    rw [hsndNorm, div_one]
    exact ENNReal.ofReal_le_ofReal (min_le_right (r / 2) (R / 2))
  -- Restrict the scalar owner to the same smaller working ball consumed by the later diagonal
  -- assembly.
  exact hBase.mono (by positivity) hRadiusLe

/-- Helper for Theorem IV.5-extra-2: the block-row owner and the sparse last-variable owner can be
packaged together on one common product ball before the final bilinear multiplication step. -/
lemma parametricPowerSeriesTermPair_hasFPowerSeriesOnCommonWorkingBall_local
    {m n : ℕ}
    {A : ℕ → (Fin (m + 1) → ℂ) → ℂ} {x0 : Fin (m + 1) → ℂ} {u0 : ℂ} {r R : ℝ}
    {P : FormalMultilinearSeries ℂ (Fin (m + 1) → ℂ) ℂ}
    (hr : 0 < r) (hR : 0 < R)
    (hP : HasFPowerSeriesOnBall (A n) P x0 (ENNReal.ofReal (r / 2))) :
    HasFPowerSeriesOnBall
      (fun q : (Fin (m + 1) → ℂ) × ℂ ↦ (A n q.1, (q.2 - u0) ^ n))
      ((P.compContinuousLinearMap (ContinuousLinearMap.fst ℂ (Fin (m + 1) → ℂ) ℂ)).prod
        (FormalMultilinearSeries.compContinuousLinearMap
          (FormalMultilinearSeries.ofScalars ℂ (fun k ↦ if k = n then (1 : ℂ) else 0))
          (ContinuousLinearMap.snd ℂ (Fin (m + 1) → ℂ) ℂ)))
      (x0, u0)
      (ENNReal.ofReal (min (r / 2) (R / 2))) := by
  have hfst :
      HasFPowerSeriesOnBall
        (fun q : (Fin (m + 1) → ℂ) × ℂ ↦ A n q.1)
        (P.compContinuousLinearMap (ContinuousLinearMap.fst ℂ (Fin (m + 1) → ℂ) ℂ))
        (x0, u0)
        (ENNReal.ofReal (min (r / 2) (R / 2))) := by
    -- Put the block-row owner on the common working radius first so the product owner can use one
    -- radius parameter throughout.
    exact
      coefficientRowCompFst_hasFPowerSeriesOnCommonWorkingBall_local
        (A := A) (x0 := x0) (u0 := u0) (r := r) (R := R) hr hR hP
  have hsnd :
      HasFPowerSeriesOnBall
        (fun q : (Fin (m + 1) → ℂ) × ℂ ↦ (q.2 - u0) ^ n)
        (FormalMultilinearSeries.compContinuousLinearMap
          (FormalMultilinearSeries.ofScalars ℂ (fun k ↦ if k = n then (1 : ℂ) else 0))
          (ContinuousLinearMap.snd ℂ (Fin (m + 1) → ℂ) ℂ))
        (x0, u0)
        (ENNReal.ofReal (min (r / 2) (R / 2))) := by
    -- Match the sparse scalar owner to the same common radius.
    exact
      centeredPowCompSnd_hasFPowerSeriesOnCommonWorkingBall_local
        (x0 := x0) (u0 := u0) (r := r) (R := R) hr hR n
  -- Package the two common-radius owners into the product-valued owner that feeds the final
  -- bilinear multiplication series.
  simpa using hfst.prod hsnd

/-- Helper for Theorem IV.5-extra-2: the canonical product-series owner for one centered
parametric term is obtained by combining the coefficient owner with the centered scalar monomial
owner through the bilinear multiplication formal series. -/
noncomputable def parametricPowerSeriesTermOwner_local
    {m : ℕ}
    (A : (Fin (m + 1) → ℂ) → ℂ) (x0 : Fin (m + 1) → ℂ) (u0 : ℂ) (n : ℕ)
    (P : FormalMultilinearSeries ℂ (Fin (m + 1) → ℂ) ℂ) :
    FormalMultilinearSeries ℂ ((Fin (m + 1) → ℂ) × ℂ) ℂ :=
  (((ContinuousLinearMap.mul ℂ ℂ).fpowerSeriesBilinear (A x0, (u0 - u0) ^ n)).comp
    ((P.compContinuousLinearMap (ContinuousLinearMap.fst ℂ (Fin (m + 1) → ℂ) ℂ)).prod
      ((FormalMultilinearSeries.ofScalars ℂ
          (fun q ↦ if q = n then (1 : ℂ) else 0)).compContinuousLinearMap
        (ContinuousLinearMap.snd ℂ (Fin (m + 1) → ℂ) ℂ))))

/-- Helper for Theorem IV.5-extra-2: the pulled-back sparse centered monomial owner has no
nonzero term in degree strictly below `n`. -/
lemma centeredPowCompSnd_apply_eq_zero_of_lt_local
    {m n k : ℕ}
    {v : Fin k → (Fin (m + 1) → ℂ) × ℂ}
    (hk : k < n) :
    ((FormalMultilinearSeries.ofScalars ℂ (fun q ↦ if q = n then (1 : ℂ) else 0)).compContinuousLinearMap
        (ContinuousLinearMap.snd ℂ (Fin (m + 1) → ℂ) ℂ))
      k v = 0 := by
  -- The sparse centered monomial owner is literally zero in every degree below `n`.
  simp [FormalMultilinearSeries.compContinuousLinearMap_apply, FormalMultilinearSeries.ofScalars,
    hk.ne]

/-- Helper for Theorem IV.5-extra-2: the explicit owner for one centered parametric term has zero
constant coefficient as soon as the centered monomial degree is positive. -/
lemma parametricPowerSeriesTermOwner_zero_local
    {m n : ℕ}
    {A : (Fin (m + 1) → ℂ) → ℂ} {x0 : Fin (m + 1) → ℂ} {u0 : ℂ}
    {P : FormalMultilinearSeries ℂ (Fin (m + 1) → ℂ) ℂ}
    (hn : 0 < n) :
    parametricPowerSeriesTermOwner_local A x0 u0 n P 0 = 0 := by
  -- In degree `0`, only the bilinear owner's constant term contributes, and it contains
  -- `(u0 - u0)^n = 0`.
  ext v
  simp [parametricPowerSeriesTermOwner_local, hn.ne']

/-- Helper for Theorem IV.5-extra-2: in the length-two composition branch for the explicit term
owner, the sparse last-variable factor already vanishes when the total degree is below `n`. -/
lemma parametricPowerSeriesTermOwner_lengthTwoSecondSlotZero_local
    {m : ℕ}
    {n k : ℕ} {P : FormalMultilinearSeries ℂ (Fin (m + 1) → ℂ) ℂ}
    {c : Composition k}
    (hk : k < n) (hc : c.length = 2)
    (v : Fin k → (Fin (m + 1) → ℂ) × ℂ) :
    ((((P.compContinuousLinearMap (ContinuousLinearMap.fst ℂ (Fin (m + 1) → ℂ) ℂ)).prod
          ((FormalMultilinearSeries.ofScalars ℂ
                (fun q ↦ if q = n then (1 : ℂ) else 0)).compContinuousLinearMap
              (ContinuousLinearMap.snd ℂ (Fin (m + 1) → ℂ) ℂ))).applyComposition c v)
        (Fin.cast hc.symm 1)).2 = 0 := by
  -- Route correction: isolate the transported second-slot zero first, so the length-two branch can
  -- later close by a single `rw` into `uncurryBilinear_apply`.
  have hslot :
      c.blocksFun (Fin.cast hc.symm 1) < n := by
    exact lt_of_le_of_lt (c.blocksFun_le (Fin.cast hc.symm 1)) hk
  -- Expand only the second product component of `applyComposition`.
  change
    ((FormalMultilinearSeries.ofScalars ℂ
          (fun q ↦ if q = n then (1 : ℂ) else 0)).compContinuousLinearMap
        (ContinuousLinearMap.snd ℂ (Fin (m + 1) → ℂ) ℂ))
      (c.blocksFun (Fin.cast hc.symm 1))
      (v ∘ c.embedding (Fin.cast hc.symm 1)) = 0
  exact centeredPowCompSnd_apply_eq_zero_of_lt_local hslot

/-- Helper for Theorem IV.5-extra-2: in the length-one composition branch for the explicit
normalized product term owner, the sparse last-variable factor already kills the branch below the
true monomial degree. -/
lemma normalizedProductTermOwner_lengthOneBranchZero_local
    {m : ℕ}
    {n k : ℕ}
    {A : (Fin (m + 1) → ℂ) → ℂ} {x0 : Fin (m + 1) → ℂ} {u0 : ℂ}
    {P : FormalMultilinearSeries ℂ (Fin (m + 1) → ℂ) ℂ}
    {c : Composition k}
    (hk : k < n) (hc : c.length = 1)
    (v : Fin k → (Fin (m + 1) → ℂ) × ℂ) :
    (((ContinuousLinearMap.mul ℂ ℂ).fpowerSeriesBilinear (A x0, (u0 - u0) ^ n)).compAlongComposition
        ((P.compContinuousLinearMap (ContinuousLinearMap.fst ℂ (Fin (m + 1) → ℂ) ℂ)).prod
          ((FormalMultilinearSeries.ofScalars ℂ
                (fun q ↦ if q = n then (1 : ℂ) else 0)).compContinuousLinearMap
            (ContinuousLinearMap.snd ℂ (Fin (m + 1) → ℂ) ℂ)))
        c) v = 0 := by
  let S :
      FormalMultilinearSeries ℂ ((Fin (m + 1) → ℂ) × ℂ) (ℂ × ℂ) :=
    (P.compContinuousLinearMap (ContinuousLinearMap.fst ℂ (Fin (m + 1) → ℂ) ℂ)).prod
      ((FormalMultilinearSeries.ofScalars ℂ
            (fun q ↦ if q = n then (1 : ℂ) else 0)).compContinuousLinearMap
        (ContinuousLinearMap.snd ℂ (Fin (m + 1) → ℂ) ℂ))
  have hkpos : 0 < k := by
    exact (c.length_pos_iff).mp (by simpa [hc] using (show 0 < 1 by decide))
  have hcSingle : c = Composition.single k hkpos :=
    (Composition.eq_single_iff_length hkpos).2 hc
  have hnpos : 0 < n := lt_of_le_of_lt (Nat.zero_le k) hk
  have hsnd :
      (S k v).2 = 0 := by
    -- Read the second component of the product owner as the sparse last-variable coefficient.
    change
      ((FormalMultilinearSeries.ofScalars ℂ
            (fun q ↦ if q = n then (1 : ℂ) else 0)).compContinuousLinearMap
        (ContinuousLinearMap.snd ℂ (Fin (m + 1) → ℂ) ℂ))
        k v = 0
    exact
      centeredPowCompSnd_apply_eq_zero_of_lt_local
        (m := m) (n := n) (k := k) (v := v) hk
  -- Route correction: normalize the unique length-one composition before evaluating the bilinear
  -- coefficient, so the sparse second slot can close the branch directly.
  subst c
  let w : Fin 1 → ℂ × ℂ := fun _ : Fin 1 ↦ S k v
  have happly : S.applyComposition (Composition.single k hkpos) v = w := by
    funext i
    fin_cases i
    simp [w, FormalMultilinearSeries.applyComposition_single S hkpos v]
  have hcomp :
      (((ContinuousLinearMap.mul ℂ ℂ).fpowerSeriesBilinear (A x0, (u0 - u0) ^ n)).compAlongComposition
          S (Composition.single k hkpos)) v =
        ((continuousMultilinearCurryFin1 ℂ (ℂ × ℂ) ℂ).symm
          ((ContinuousLinearMap.mul ℂ ℂ).deriv₂ (A x0, (u0 - u0) ^ n))) w := by
    rw [FormalMultilinearSeries.compAlongComposition_apply, happly]
    rfl
  rw [hcomp, continuousMultilinearCurryFin1_symm_apply, ContinuousLinearMap.coe_deriv₂]
  simpa [w, hsnd, hnpos.ne']

/-- Helper for Theorem IV.5-extra-2: in the length-two composition branch for the explicit
normalized product term owner, the sparse second slot of the product owner forces the branch to
vanish below the monomial degree. -/
lemma normalizedProductTermOwner_lengthTwoBranchZero_local
    {m : ℕ}
    {n k : ℕ}
    {A : (Fin (m + 1) → ℂ) → ℂ} {x0 : Fin (m + 1) → ℂ} {u0 : ℂ}
    {P : FormalMultilinearSeries ℂ (Fin (m + 1) → ℂ) ℂ}
    {c : Composition k}
    (hk : k < n) (hc : c.length = 2)
    (v : Fin k → (Fin (m + 1) → ℂ) × ℂ) :
    (((ContinuousLinearMap.mul ℂ ℂ).fpowerSeriesBilinear (A x0, (u0 - u0) ^ n)).compAlongComposition
        ((P.compContinuousLinearMap (ContinuousLinearMap.fst ℂ (Fin (m + 1) → ℂ) ℂ)).prod
          ((FormalMultilinearSeries.ofScalars ℂ
                (fun q ↦ if q = n then (1 : ℂ) else 0)).compContinuousLinearMap
            (ContinuousLinearMap.snd ℂ (Fin (m + 1) → ℂ) ℂ)))
        c) v = 0 := by
  let S :
      FormalMultilinearSeries ℂ ((Fin (m + 1) → ℂ) × ℂ) (ℂ × ℂ) :=
    (P.compContinuousLinearMap (ContinuousLinearMap.fst ℂ (Fin (m + 1) → ℂ) ℂ)).prod
      ((FormalMultilinearSeries.ofScalars ℂ
            (fun q ↦ if q = n then (1 : ℂ) else 0)).compContinuousLinearMap
        (ContinuousLinearMap.snd ℂ (Fin (m + 1) → ℂ) ℂ))
  let w : Fin 2 → ℂ × ℂ := fun i ↦ S.applyComposition c v (Fin.cast hc.symm i)
  have hsnd : (w 1).2 = 0 := by
    -- Read the transported second slot through the dedicated sparse-owner vanishing bridge first.
    simpa [w, S] using
      parametricPowerSeriesTermOwner_lengthTwoSecondSlotZero_local
        (m := m) (n := n) (k := k) (P := P) (c := c) hk hc v
  have htransport :
      ∀ {N : ℕ} (hN : N = 2) (f : Fin N → ℂ × ℂ),
        (((ContinuousLinearMap.mul ℂ ℂ).fpowerSeriesBilinear (A x0, (u0 - u0) ^ n)) N) f =
          (((ContinuousLinearMap.mul ℂ ℂ).fpowerSeriesBilinear (A x0, (u0 - u0) ^ n)) 2)
            (fun i ↦ f (Fin.cast hN.symm i)) := by
    intro N hN f
    -- Transport the coefficient evaluation through a plain natural-number equality before
    -- specializing back to the composition length.
    cases hN
    rfl
  -- Route correction: rewrite the outer degree-two bilinear coefficient to `uncurryBilinear`, then
  -- the branch dies because the sparse second slot is already zero.
  rw [FormalMultilinearSeries.compAlongComposition_apply, htransport hc (S.applyComposition c v),
    ContinuousLinearMap.fpowerSeriesBilinear_apply_two,
    ContinuousLinearMap.uncurryBilinear_apply]
  simpa [w, hsnd]

/-- Helper for Theorem IV.5-extra-2: the canonical owner of the `n`th normalized product term has
no coefficient of total degree `k < n`. -/
lemma normalizedProductTermOwnerCoeff_eq_zero_of_lt_local
    {m : ℕ}
    {n k : ℕ}
    {A : (Fin (m + 1) → ℂ) → ℂ} {x0 : Fin (m + 1) → ℂ} {u0 : ℂ}
    {P : FormalMultilinearSeries ℂ (Fin (m + 1) → ℂ) ℂ}
    (hk : k < n) :
    parametricPowerSeriesTermOwner_local A x0 u0 n P k = 0 := by
  by_cases hkzero : k = 0
  · subst k
    -- The constant coefficient is already isolated by the earlier explicit zero-degree lemma.
    exact
      parametricPowerSeriesTermOwner_zero_local
        (A := A) (x0 := x0) (u0 := u0) (P := P) hk
  · have hkpos : 0 < k := Nat.pos_of_ne_zero hkzero
    ext v
    -- Expand the composed owner once, then kill each composition branch by its length.
    rw [parametricPowerSeriesTermOwner_local, FormalMultilinearSeries.comp]
    rw [ContinuousMultilinearMap.sum_apply]
    refine Finset.sum_eq_zero ?_
    intro c hcComp
    by_cases hlen1 : c.length = 1
    · exact normalizedProductTermOwner_lengthOneBranchZero_local hk hlen1 v
    · by_cases hlen2 : c.length = 2
      · exact normalizedProductTermOwner_lengthTwoBranchZero_local hk hlen2 v
      · have hlenpos : 0 < c.length := c.length_pos_of_pos hkpos
        have hlen_ge_three : 3 ≤ c.length := by
          omega
        -- Every remaining branch lands in an outer bilinear coefficient of degree at least `3`.
        have hbil_zero :
            (ContinuousLinearMap.mul ℂ ℂ).fpowerSeriesBilinear (A x0, (u0 - u0) ^ n) c.length = 0 := by
          obtain ⟨d, hd⟩ := Nat.exists_eq_add_of_le hlen_ge_three
          rw [hd, add_comm]
          simpa using
            (ContinuousLinearMap.fpowerSeriesBilinear_apply_add_three
              (f := ContinuousLinearMap.mul ℂ ℂ) (x := (A x0, (u0 - u0) ^ n)) d)
        rw [FormalMultilinearSeries.compAlongComposition_apply, hbil_zero]
        simp

/-- Helper for Theorem IV.5-extra-2: one centered parametric term now has an explicit canonical
joint owner, so later coefficient-level lemmas can refer to the owner directly instead of
re-opening an existential witness. -/
lemma parametricPowerSeriesTerm_hasFPowerSeriesAt_explicit_local
    {m : ℕ}
    {A : (Fin (m + 1) → ℂ) → ℂ} {x0 : Fin (m + 1) → ℂ} {u0 : ℂ} {n : ℕ}
    {P : FormalMultilinearSeries ℂ (Fin (m + 1) → ℂ) ℂ}
    (hA : HasFPowerSeriesAt A P x0) :
    HasFPowerSeriesAt
      (fun p : (Fin (m + 1) → ℂ) × ℂ ↦ A p.1 * (p.2 - u0) ^ n)
      (parametricPowerSeriesTermOwner_local A x0 u0 n P)
      (x0, u0) := by
  have hPow :
      HasFPowerSeriesAt
        (fun u : ℂ ↦ (u - u0) ^ n)
        (FormalMultilinearSeries.ofScalars ℂ (fun q ↦ if q = n then (1 : ℂ) else 0))
        u0 := by
    -- Route correction: use the sparse centered monomial owner, so later support lemmas can read
    -- lower-degree vanishing directly from the owner instead of reopening derivative algebra.
    exact centeredPow_hasFPowerSeriesAt_sparse_local n
  -- Compose the block-variable owner with the scalar monomial owner through multiplication once.
  simpa [parametricPowerSeriesTermOwner_local] using
    hasFPowerSeriesAt_mul_comp_fst_snd hA hPow

/-- Helper for Theorem IV.5-extra-2: any concrete power-series witness for one coefficient row
already gives an explicit neighborhood on which the canonical joint owner sums to the centered
parametric term. -/
lemma parametricPowerSeriesTerm_eq_ownerSumOnEball_of_hasFPowerSeriesAt_local
    {m : ℕ}
    {A : (Fin (m + 1) → ℂ) → ℂ} {x0 : Fin (m + 1) → ℂ} {u0 : ℂ} {n : ℕ}
    {P : FormalMultilinearSeries ℂ (Fin (m + 1) → ℂ) ℂ}
    (hA : HasFPowerSeriesAt A P x0) :
    ∃ ρ : ENNReal, (0 < ρ) ∧
      Set.EqOn
        (fun q : (Fin (m + 1) → ℂ) × ℂ ↦
          (parametricPowerSeriesTermOwner_local A x0 u0 n P).sum (q - (x0, u0)))
        (fun q : (Fin (m + 1) → ℂ) × ℂ ↦ A q.1 * (q.2 - u0) ^ n)
        (Metric.eball (x0, u0) ρ) := by
  rcases
      parametricPowerSeriesTerm_hasFPowerSeriesAt_explicit_local
        (A := A) (x0 := x0) (u0 := u0) (n := n) (P := P) hA with
    ⟨ρ, hρ⟩
  refine ⟨ρ, hρ.r_pos, ?_⟩
  intro q hq
  have hsub : q - (x0, u0) ∈ Metric.eball (0 : (Fin (m + 1) → ℂ) × ℂ) ρ := by
    -- Rewrite the displaced point into the zero-centered eball expected by the owner sum API.
    simpa [Metric.mem_eball, edist_eq_enorm_sub] using hq
  -- Evaluate the explicit owner on the concrete displacement inside its convergence ball.
  simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using
    (hρ.sum (y := q - (x0, u0)) hsub).symm

/-- Helper for Theorem IV.5-extra-2: once one coefficient row is already known on a concrete ball,
the canonical centered term owner has the expected germ at the product center without reopening
the multiplication construction. -/
lemma parametricPowerSeriesTerm_hasFPowerSeriesAt_of_ballOwner_local
    {m n : ℕ}
    {A : ℕ → (Fin (m + 1) → ℂ) → ℂ} {x0 : Fin (m + 1) → ℂ} {u0 : ℂ} {r : ℝ}
    {P : FormalMultilinearSeries ℂ (Fin (m + 1) → ℂ) ℂ}
    (hP : HasFPowerSeriesOnBall (A n) P x0 (ENNReal.ofReal (r / 2))) :
    HasFPowerSeriesAt
      (fun q : (Fin (m + 1) → ℂ) × ℂ ↦ A n q.1 * (q.2 - u0) ^ n)
      (parametricPowerSeriesTermOwner_local (A n) x0 u0 n P)
      (x0, u0) := by
  -- Collapse the concrete ball owner back to the center germ before invoking the explicit
  -- multiplication owner already proved above.
  exact
    parametricPowerSeriesTerm_hasFPowerSeriesAt_explicit_local
      (A := A n) (x0 := x0) (u0 := u0) (n := n) (P := P) hP.hasFPowerSeriesAt

/-- Helper for Theorem IV.5-extra-2: a concrete ball owner for one coefficient row already yields a
product-space neighborhood where the explicit centered term owner matches the corresponding term. -/
lemma parametricPowerSeriesTerm_eq_ownerSumOnSomeEball_of_ballOwner_local
    {m n : ℕ}
    {A : ℕ → (Fin (m + 1) → ℂ) → ℂ} {x0 : Fin (m + 1) → ℂ} {u0 : ℂ} {r : ℝ}
    {P : FormalMultilinearSeries ℂ (Fin (m + 1) → ℂ) ℂ}
    (hP : HasFPowerSeriesOnBall (A n) P x0 (ENNReal.ofReal (r / 2))) :
    ∃ ρ : ENNReal, (0 < ρ) ∧
      Set.EqOn
        (fun q : (Fin (m + 1) → ℂ) × ℂ ↦
          (parametricPowerSeriesTermOwner_local (A n) x0 u0 n P).sum (q - (x0, u0)))
        (fun q : (Fin (m + 1) → ℂ) × ℂ ↦ A n q.1 * (q.2 - u0) ^ n)
        (Metric.eball (x0, u0) ρ) := by
  -- Reuse the center-germ equality package, but now with the concrete row owner frozen once for
  -- the later working-ball assembly.
  exact
    parametricPowerSeriesTerm_eq_ownerSumOnEball_of_hasFPowerSeriesAt_local
      (A := A n) (x0 := x0) (u0 := u0) (n := n) (P := P) hP.hasFPowerSeriesAt

/-- Helper for Theorem IV.5-extra-2: analyticity of one coefficient row at the block center already
produces a concrete neighborhood where the canonical joint owner equals the corresponding centered
parametric term. -/
lemma parametricPowerSeriesTerm_eq_ownerSumOnSomeEball_local
    {m : ℕ}
    {A : (Fin (m + 1) → ℂ) → ℂ} {x0 : Fin (m + 1) → ℂ} {u0 : ℂ} {n : ℕ}
    (hA : AnalyticAt ℂ A x0) :
    ∃ P : FormalMultilinearSeries ℂ (Fin (m + 1) → ℂ) ℂ,
      ∃ ρ : ENNReal, (0 < ρ) ∧
        Set.EqOn
          (fun q : (Fin (m + 1) → ℂ) × ℂ ↦
            (parametricPowerSeriesTermOwner_local A x0 u0 n P).sum (q - (x0, u0)))
          (fun q : (Fin (m + 1) → ℂ) × ℂ ↦ A q.1 * (q.2 - u0) ^ n)
          (Metric.eball (x0, u0) ρ) := by
  rcases hA with ⟨P, hP⟩
  -- Freeze the analytic-at-center witness once, then pass to the explicit joint owner.
  exact ⟨P, parametricPowerSeriesTerm_eq_ownerSumOnEball_of_hasFPowerSeriesAt_local hP⟩

/-- Helper for Theorem IV.5-extra-2: the total centered owner is packaged degreewise by summing
the canonical term owners along each diagonal `n ≤ k`. -/
noncomputable def centeredParametricSeriesDiagonalOwner_local
    {m : ℕ}
    (T : ℕ → FormalMultilinearSeries ℂ ((Fin (m + 1) → ℂ) × ℂ) ℂ) :
    FormalMultilinearSeries ℂ ((Fin (m + 1) → ℂ) × ℂ) ℂ :=
  fun k ↦ Finset.sum (Finset.range (k + 1)) (fun n ↦ T n k)

/-- Helper for Theorem IV.5-extra-2: the diagonal owner's finite truncations expand to the expected
finite double sum in the fixed diagonal normal form. -/
lemma centeredParametricSeriesDiagonalOwner_partialSum_apply_local
    {m : ℕ}
    (T : ℕ → FormalMultilinearSeries ℂ ((Fin (m + 1) → ℂ) × ℂ) ℂ)
    (N : ℕ) (y : (Fin (m + 1) → ℂ) × ℂ) :
    (centeredParametricSeriesDiagonalOwner_local T).partialSum N y =
      ∑ k ∈ Finset.range N, ∑ n ∈ Finset.range (k + 1), T n k (fun _ ↦ y) := by
  -- Expand `partialSum` once so later comparisons can stay in one coefficient spelling.
  simp [FormalMultilinearSeries.partialSum, centeredParametricSeriesDiagonalOwner_local]

/-- Helper for Theorem IV.5-extra-2: increasing the diagonal owner's truncation from `N` to `N + 1`
adds exactly the new total-degree-`N` layer. -/
lemma centeredParametricSeriesDiagonalOwner_partialSum_succ_local
    {m : ℕ}
    (T : ℕ → FormalMultilinearSeries ℂ ((Fin (m + 1) → ℂ) × ℂ) ℂ)
    (N : ℕ) (y : (Fin (m + 1) → ℂ) × ℂ) :
    (centeredParametricSeriesDiagonalOwner_local T).partialSum (N + 1) y =
      (centeredParametricSeriesDiagonalOwner_local T).partialSum N y +
        ∑ n ∈ Finset.range (N + 1), T n N (fun _ ↦ y) := by
  -- Split the total-degree truncation at the last degree so the remaining blocker is visible as a
  -- degree-layer mismatch rather than hidden inside the nested sum.
  rw [centeredParametricSeriesDiagonalOwner_partialSum_apply_local,
    centeredParametricSeriesDiagonalOwner_partialSum_apply_local, Finset.sum_range_succ]

/-- Helper for Theorem IV.5-extra-2: a centered `HasFPowerSeriesAt` germ already contains a
concrete positive-radius ball owner for the same formal series. -/
lemma hasFPowerSeriesAt_exists_ballOwner_local
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    {f : E → ℂ} {P : FormalMultilinearSeries ℂ E ℂ} {x : E}
    (h : HasFPowerSeriesAt f P x) :
    ∃ r, HasFPowerSeriesOnBall f P x r := by
  -- `HasFPowerSeriesAt` is defined by existence of such a concrete ball owner.
  exact h

/-- Helper for Theorem IV.5-extra-2: an analytic coefficient row at the block center already
produces the explicit joint product-space owner for the corresponding centered parametric term. -/
lemma analyticAtParametricPowerSeriesTerm_hasExplicitOwner_local
    {m : ℕ}
    {A : (Fin (m + 1) → ℂ) → ℂ} {x0 : Fin (m + 1) → ℂ} {u0 : ℂ} {n : ℕ}
    (hA : AnalyticAt ℂ A x0) :
    ∃ Q : FormalMultilinearSeries ℂ ((Fin (m + 1) → ℂ) × ℂ) ℂ,
      HasFPowerSeriesAt
        (fun q : (Fin (m + 1) → ℂ) × ℂ ↦ A q.1 * (q.2 - u0) ^ n)
        Q
        (x0, u0) := by
  rcases hA with ⟨P, hP⟩
  refine ⟨parametricPowerSeriesTermOwner_local A x0 u0 n P, ?_⟩
  -- Reuse the explicit owner so the remaining centered-series frontier only has to sum these
  -- term-level owners and compare its total sum with the target `tsum`.
  exact
    parametricPowerSeriesTerm_hasFPowerSeriesAt_explicit_local hP

/-- Helper for Theorem IV.5-extra-2: coefficient-row analyticity on the ambient block ball already
packages each centered parametric term with an explicit product-space owner at the center. -/
lemma coefficientRowTermHasExplicitOwnerAtCenter_local
    {m : ℕ}
    {A : ℕ → (Fin (m + 1) → ℂ) → ℂ} {x0 : Fin (m + 1) → ℂ} {u0 : ℂ} {r : ℝ}
    (hr : 0 < r)
    (hCoeffOn : ∀ n : ℕ, AnalyticOnNhd ℂ (A n) (Metric.ball x0 r)) :
    ∀ n : ℕ,
      ∃ Q : FormalMultilinearSeries ℂ ((Fin (m + 1) → ℂ) × ℂ) ℂ,
        HasFPowerSeriesAt
          (fun q : (Fin (m + 1) → ℂ) × ℂ ↦ A n q.1 * (q.2 - u0) ^ n)
          Q
          (x0, u0) := by
  have hx0 : x0 ∈ Metric.ball x0 r := by
    -- The block-center belongs to the ambient coefficient domain, so every row can be frozen
    -- there before the diagonal owner is assembled.
    simpa [Metric.mem_ball] using hr
  intro n
  -- Delegate the product-space owner construction to the explicit one-row term package.
  exact
    analyticAtParametricPowerSeriesTerm_hasExplicitOwner_local (hCoeffOn n x0 hx0)

/-- Helper for Theorem IV.5-extra-2: every analytic coefficient row on the ambient block ball
already carries the canonical Taylor family `ftaylorSeries ℂ (A n)` on that same ball. -/
lemma coefficientRowHasFTaylorSeriesUpToOn_local
    {m : ℕ}
    {A : ℕ → (Fin (m + 1) → ℂ) → ℂ} {x0 : Fin (m + 1) → ℂ} {r : ℝ}
    (hCoeffOn : ∀ n : ℕ, AnalyticOnNhd ℂ (A n) (Metric.ball x0 r)) :
    ∀ n : ℕ,
      HasFTaylorSeriesUpToOn ⊤ (A n) (ftaylorSeries ℂ (A n)) (Metric.ball x0 r) := by
  intro n
  -- Use the canonical Taylor family attached to an analytic function on a neighborhood.
  exact (hCoeffOn n).hasFTaylorSeriesUpToOn ⊤

/-- Helper for Theorem IV.5-extra-2: the strict half-radius block ball stays inside the original
ambient coefficient ball. -/
lemma halfBlockBall_subset_ambient_local
    {m : ℕ} {x0 : Fin (m + 1) → ℂ} {r : ℝ}
    (hr : 0 < r) :
    Metric.ball x0 (r / 2) ⊆ Metric.ball x0 r := by
  intro x hx
  -- Compare the half-radius membership inequality directly with the ambient radius.
  have hxdist : dist x x0 < r / 2 := by
    simpa [Metric.mem_ball] using hx
  have hhalf_lt : r / 2 < r := by
    linarith
  simpa [Metric.mem_ball] using lt_of_lt_of_le hxdist hhalf_lt.le

/-- Helper for Theorem IV.5-extra-2: every coefficient row remains analytic on the smaller
half-radius block ball centered at `x0`. -/
lemma coefficientRowAnalyticOnNhd_halfBall_local
    {m : ℕ}
    {A : ℕ → (Fin (m + 1) → ℂ) → ℂ} {x0 : Fin (m + 1) → ℂ} {r : ℝ}
    (hr : 0 < r)
    (hCoeffOn : ∀ n : ℕ, AnalyticOnNhd ℂ (A n) (Metric.ball x0 r)) :
    ∀ n : ℕ, AnalyticOnNhd ℂ (A n) (Metric.ball x0 (r / 2)) := by
  intro n
  -- Restrict the ambient analytic neighborhood package to the smaller working half ball once.
  exact (hCoeffOn n).mono (halfBlockBall_subset_ambient_local (m := m) (x0 := x0) hr)

/-- Helper for Theorem IV.5-extra-2: after shrinking to the half-radius block ball, each
coefficient row still carries the canonical `ftaylorSeries` family there. -/
lemma coefficientRowHasFTaylorSeriesUpToOn_halfBall_local
    {m : ℕ}
    {A : ℕ → (Fin (m + 1) → ℂ) → ℂ} {x0 : Fin (m + 1) → ℂ} {r : ℝ}
    (hr : 0 < r)
    (hCoeffOn : ∀ n : ℕ, AnalyticOnNhd ℂ (A n) (Metric.ball x0 r)) :
    ∀ n : ℕ,
      HasFTaylorSeriesUpToOn ⊤ (A n) (ftaylorSeries ℂ (A n)) (Metric.ball x0 (r / 2)) := by
  intro n
  -- Freeze the same canonical Taylor family on the smaller ball instead of reopening the ambient
  -- analyticity package later in the owner construction.
  exact
    (coefficientRowHasFTaylorSeriesUpToOn_local (A := A) (x0 := x0) (r := r) hCoeffOn n).mono
      (halfBlockBall_subset_ambient_local (m := m) (x0 := x0) hr)

/-- Helper for Theorem IV.5-extra-2: the uniform geometric coefficient control already gives one
uniform `HasSum` package on the small working product ball around `(x0, u0)`. -/
lemma centeredParametricSeries_hasSumUniformlyOnWorkingBall_local
    {m : ℕ}
    {A : ℕ → (Fin (m + 1) → ℂ) → ℂ} {x0 : Fin (m + 1) → ℂ} {u0 : ℂ}
    {r R C : ℝ}
    (hR : 0 < R)
    (hCoeffBound : ∀ x ∈ Metric.closedBall x0 (r / 2), ∀ n : ℕ, ‖A n x‖ ≤ C / R ^ n) :
    HasSumUniformlyOn
      (fun n : ℕ ↦ fun q : (Fin (m + 1) → ℂ) × ℂ ↦ A n q.1 * (q.2 - u0) ^ n)
      (fun q : (Fin (m + 1) → ℂ) × ℂ ↦ ∑' n : ℕ, A n q.1 * (q.2 - u0) ^ n)
      (Metric.ball (x0, u0) (min (r / 2) (R / 2))) := by
  have hmajorant : Summable (fun n : ℕ ↦ max C 0 * (1 / 2 : ℝ) ^ n) := by
    -- Use `max C 0` so the majorant is globally nonnegative even when the working ball is empty.
    simpa [mul_assoc] using (summable_geometric_two.mul_left (max C 0))
  refine HasSumUniformlyOn.of_norm_le_summable hmajorant ?_
  intro n q hq
  rcases
      centeredProductWorkingBall_mem_local hq with
    ⟨hqBlock, hqLast⟩
  -- On the actual working ball the coefficient constant is forced to be nonnegative, so the
  -- existing geometric term estimate upgrades to the global `max C 0` majorant.
  calc
    ‖A n q.1 * (q.2 - u0) ^ n‖ ≤ C * (1 / 2 : ℝ) ^ n := by
      exact
        normalizedProductCauchySeries_termBound_local
          hR hCoeffBound n q ⟨hqBlock, hqLast⟩
    _ ≤ max C 0 * (1 / 2 : ℝ) ^ n := by
      exact mul_le_mul_of_nonneg_right (le_max_left C 0) (by positivity)

/-- Helper for Theorem IV.5-extra-2: the centered partial sums converge uniformly on the working
product ball to the target `tsum`. -/
lemma centeredParametricSeries_partialSums_tendstoUniformlyOnWorkingBall_local
    {m : ℕ}
    {A : ℕ → (Fin (m + 1) → ℂ) → ℂ} {x0 : Fin (m + 1) → ℂ} {u0 : ℂ}
    {r R C : ℝ}
    (hR : 0 < R)
    (hCoeffBound : ∀ x ∈ Metric.closedBall x0 (r / 2), ∀ n : ℕ, ‖A n x‖ ≤ C / R ^ n) :
    TendstoUniformlyOn
      (fun N : ℕ ↦ fun q : (Fin (m + 1) → ℂ) × ℂ ↦
        ∑ n ∈ Finset.range N, A n q.1 * (q.2 - u0) ^ n)
      (fun q : (Fin (m + 1) → ℂ) × ℂ ↦ ∑' n : ℕ, A n q.1 * (q.2 - u0) ^ n)
      Filter.atTop
      (Metric.ball (x0, u0) (min (r / 2) (R / 2))) := by
  -- Repackage the uniform `HasSum` statement into the corresponding finite-partial-sum limit.
  simpa using
    HasSumUniformlyOn.tendstoUniformlyOn_finsetRange
      (centeredParametricSeries_hasSumUniformlyOnWorkingBall_local
        hR hCoeffBound)

/-- Helper for Theorem IV.5-extra-2: every finite centered partial sum is jointly analytic on the
ambient product neighborhood coming from the coefficient ball and the half-radius last-variable
disc. -/
lemma centeredParametricPartialSums_analyticOnAmbientProdBall_local
    {m : ℕ}
    {A : ℕ → (Fin (m + 1) → ℂ) → ℂ} {x0 : Fin (m + 1) → ℂ} {u0 : ℂ}
    {r R : ℝ}
    (hCoeffOn : ∀ n : ℕ, AnalyticOnNhd ℂ (A n) (Metric.ball x0 r)) :
    ∀ N : ℕ,
      AnalyticOnNhd ℂ
        (fun p : (Fin (m + 1) → ℂ) × ℂ ↦
          ∑ n ∈ Finset.range N, A n p.1 * (p.2 - u0) ^ n)
        (Metric.ball x0 r ×ˢ Metric.ball u0 (R / 2)) := by
  intro N
  -- Expand the finite centered series termwise so each summand can use the existing block and
  -- last-variable analytic-on-neighborhood APIs directly.
  refine Finset.analyticOnNhd_fun_sum (Finset.range N) ?_
  intro n hn
  have hBlockOn :
      AnalyticOnNhd ℂ
        (fun p : (Fin (m + 1) → ℂ) × ℂ ↦ A n p.1)
        (Metric.ball x0 r ×ˢ Metric.ball u0 (R / 2)) := by
    refine (hCoeffOn n).comp (analyticOnNhd_fst (𝕜 := ℂ)
      (t := Metric.ball x0 r ×ˢ Metric.ball u0 (R / 2))) ?_
    intro p hp
    exact hp.1
  have hPowOn :
      AnalyticOnNhd ℂ
        (fun p : (Fin (m + 1) → ℂ) × ℂ ↦ (p.2 - u0) ^ n)
        (Metric.ball x0 r ×ˢ Metric.ball u0 (R / 2)) := by
    exact
      (((analyticOnNhd_snd (𝕜 := ℂ)
          (t := Metric.ball x0 r ×ˢ Metric.ball u0 (R / 2))).sub
        analyticOnNhd_const).pow n)
  simpa using hBlockOn.mul hPowOn

/-- Helper for Theorem IV.5-extra-2: the uniform geometric majorant already upgrades the centered
series to a continuous function on the concrete working product ball. -/
lemma centeredParametricSeries_continuousOnWorkingBall_local
    {m : ℕ}
    {A : ℕ → (Fin (m + 1) → ℂ) → ℂ} {x0 : Fin (m + 1) → ℂ} {u0 : ℂ}
    {r R C : ℝ}
    (hr : 0 < r) (hR : 0 < R)
    (hCoeffOn : ∀ n : ℕ, AnalyticOnNhd ℂ (A n) (Metric.ball x0 r))
    (hCoeffBound : ∀ x ∈ Metric.closedBall x0 (r / 2), ∀ n : ℕ, ‖A n x‖ ≤ C / R ^ n) :
    ContinuousOn
      (fun q : (Fin (m + 1) → ℂ) × ℂ ↦ ∑' n : ℕ, A n q.1 * (q.2 - u0) ^ n)
      (Metric.ball (x0, u0) (min (r / 2) (R / 2))) := by
  have hTendsto :
      TendstoUniformlyOn
        (fun N : ℕ ↦ fun q : (Fin (m + 1) → ℂ) × ℂ ↦
          ∑ n ∈ Finset.range N, A n q.1 * (q.2 - u0) ^ n)
        (fun q : (Fin (m + 1) → ℂ) × ℂ ↦ ∑' n : ℕ, A n q.1 * (q.2 - u0) ^ n)
        Filter.atTop
        (Metric.ball (x0, u0) (min (r / 2) (R / 2))) := by
    exact centeredParametricSeries_partialSums_tendstoUniformlyOnWorkingBall_local
      (A := A) (x0 := x0) (u0 := u0) (r := r) (R := R) (C := C) hR hCoeffBound
  -- Use the ambient product-ball analyticity of every finite partial sum to get continuity on the
  -- smaller concrete working ball consumed later by the centered-series closeout.
  refine hTendsto.continuousOn ?_
  show ∃ᶠ N : ℕ in Filter.atTop,
      ContinuousOn
        (fun q : (Fin (m + 1) → ℂ) × ℂ ↦
          ∑ n ∈ Finset.range N, A n q.1 * (q.2 - u0) ^ n)
        (Metric.ball (x0, u0) (min (r / 2) (R / 2)))
  refine Filter.Frequently.of_forall fun N ↦ ?_
  have hPartialOn :
      AnalyticOnNhd ℂ
        (fun q : (Fin (m + 1) → ℂ) × ℂ ↦
          ∑ n ∈ Finset.range N, A n q.1 * (q.2 - u0) ^ n)
        (Metric.ball x0 r ×ˢ Metric.ball u0 (R / 2)) := by
    exact centeredParametricPartialSums_analyticOnAmbientProdBall_local
      (A := A) (x0 := x0) (u0 := u0) (r := r) (R := R) hCoeffOn N
  refine hPartialOn.continuousOn.mono ?_
  intro q hq
  rcases centeredProductWorkingBall_mem_local hq with ⟨hqBlock, hqLast⟩
  constructor
  · have hBlockLe : dist q.1 x0 ≤ r / 2 := by
      simpa [Metric.mem_closedBall] using hqBlock
    have hHalfLt : r / 2 < r := by
      linarith
    simpa [Metric.mem_ball] using lt_of_le_of_lt hBlockLe hHalfLt
  · exact hqLast

/-- Helper for Theorem IV.5-extra-2: the centered parametric series is already separately analytic
on the small product ball coming from the block and last-variable radii. -/
lemma centeredParametricSeries_separatelyAnalyticOnProdBall_local
    {m : ℕ}
    (ih : ∀ {D' : Set (Fin (m + 1) → ℂ)} {f' : (Fin (m + 1) → ℂ) → ℂ},
      IsOpen D' →
      (∀ z ∈ D', ∀ i : Fin (m + 1), AnalyticAt ℂ (fun w ↦ f' (Function.update z i w)) (z i)) →
      AnalyticOnNhd ℂ f' D')
    {A : ℕ → (Fin (m + 1) → ℂ) → ℂ} {x0 : Fin (m + 1) → ℂ} {u0 : ℂ}
    {r R C : ℝ}
    (hr : 0 < r) (hR : 0 < R)
    (hCoeffOn : ∀ n : ℕ, AnalyticOnNhd ℂ (A n) (Metric.ball x0 r))
    (hCoeffBound : ∀ x ∈ Metric.closedBall x0 (r / 2), ∀ n : ℕ, ‖A n x‖ ≤ C / R ^ n) :
    ∀ q ∈ Metric.ball x0 (r / 2) ×ˢ Metric.ball u0 (R / 2),
      AnalyticAt ℂ
          (fun x : Fin (m + 1) → ℂ ↦
            ∑' n : ℕ, A n x * (q.2 - u0) ^ n)
          q.1 ∧
        AnalyticAt ℂ
          (fun u : ℂ ↦
            ∑' n : ℕ, A n q.1 * (u - u0) ^ n)
          q.2 := by
  let r1 : ℝ := r / 2
  have hCnonneg : 0 ≤ C := by
    have hx0Closed : x0 ∈ Metric.closedBall x0 r1 := by
      -- The block center lies in the smaller closed ball where the coefficient majorant is stated.
      simpa [Metric.mem_closedBall, r1] using (show 0 ≤ r / 2 by positivity)
    have hzero : ‖A 0 x0‖ ≤ C := by
      -- Read the zeroth coefficient bound at the center to recover the sign of the global constant.
      simpa [r1, pow_zero] using hCoeffBound x0 hx0Closed 0
    exact le_trans (norm_nonneg _) hzero
  have hLastSlices :
      ∀ x ∈ Metric.ball x0 r1,
        AnalyticOnNhd ℂ
          (fun u : ℂ ↦ ∑' n : ℕ, A n x * (u - u0) ^ n)
          (Metric.ball u0 (R / 2)) := by
    intro x hx
    have hxClosed : x ∈ Metric.closedBall x0 r1 := Metric.ball_subset_closedBall hx
    -- Freeze the block point and use the scalar geometric-series owner on the last-variable disc.
    simpa [r1] using
      analyticOnNhd_centeredScalarSeries_of_geometricCoeffBound_local
        (a := fun n : ℕ ↦ A n x) (u0 := u0) (R := R) (C := C)
        hR hCnonneg (hCoeffBound x hxClosed)
  have hBlockSlices :
      ∀ u ∈ Metric.ball u0 (R / 2),
        AnalyticOnNhd ℂ
          (fun x : Fin (m + 1) → ℂ ↦ ∑' n : ℕ, A n x * (u - u0) ^ n)
          (Metric.ball x0 r1) := by
    -- Reuse the lower-dimensional Hartogs induction on the smaller block ball.
    simpa [r1] using
      analyticOnNhd_blockParametricPowerSeries_of_uniformCoeffBound_local
        (m := m) ih (x0 := x0) (u0 := u0) (r := r) (R := R) (C := C)
        hr hR hCoeffOn hCoeffBound
  intro q hq
  constructor
  · -- Fix the last variable and read off the block-variable analytic germ from the block owner.
    exact hBlockSlices q.2 hq.2 q.1 hq.1
  · -- Fix the block point and read off the scalar analytic germ from the disc owner.
    exact hLastSlices q.1 hq.1 q.2 hq.2

/-- Helper for Theorem IV.5-extra-2: before the final Hartogs closeout, the centered parametric
series already carries the exact continuity-plus-separate-analyticity package on its natural
working neighborhoods. -/
lemma centeredParametricSeries_workingBallPackage_local
    {m : ℕ}
    (ih : ∀ {D' : Set (Fin (m + 1) → ℂ)} {f' : (Fin (m + 1) → ℂ) → ℂ},
      IsOpen D' →
      (∀ z ∈ D', ∀ i : Fin (m + 1), AnalyticAt ℂ (fun w ↦ f' (Function.update z i w)) (z i)) →
      AnalyticOnNhd ℂ f' D')
    {A : ℕ → (Fin (m + 1) → ℂ) → ℂ} {x0 : Fin (m + 1) → ℂ} {u0 : ℂ}
    {r R C : ℝ}
    (hr : 0 < r) (hR : 0 < R)
    (hCoeffOn : ∀ n : ℕ, AnalyticOnNhd ℂ (A n) (Metric.ball x0 r))
    (hCoeffBound : ∀ x ∈ Metric.closedBall x0 (r / 2), ∀ n : ℕ, ‖A n x‖ ≤ C / R ^ n) :
    ContinuousOn
        (fun q : (Fin (m + 1) → ℂ) × ℂ ↦
          ∑' n : ℕ, A n q.1 * (q.2 - u0) ^ n)
        (Metric.ball (x0, u0) (min (r / 2) (R / 2))) ∧
      ∀ q ∈ Metric.ball x0 (r / 2) ×ˢ Metric.ball u0 (R / 2),
        AnalyticAt ℂ
            (fun x : Fin (m + 1) → ℂ ↦
              ∑' n : ℕ, A n x * (q.2 - u0) ^ n)
            q.1 ∧
          AnalyticAt ℂ
            (fun u : ℂ ↦
              ∑' n : ℕ, A n q.1 * (u - u0) ^ n)
            q.2 := by
  constructor
  · -- Keep the continuity surface explicit so the final frontier is only the separate-to-joint
    -- upgrade, not another majorant or uniform-convergence reconstruction.
    exact
      centeredParametricSeries_continuousOnWorkingBall_local
        (A := A) (x0 := x0) (u0 := u0) (r := r) (R := R) (C := C)
        hr hR hCoeffOn hCoeffBound
  · -- Read the separate analyticity package off the already-isolated block and scalar slice
    -- owners on the product half-ball.
    exact
      centeredParametricSeries_separatelyAnalyticOnProdBall_local
        (m := m) ih (A := A) (x0 := x0) (u0 := u0) (r := r) (R := R) (C := C)
        hr hR hCoeffOn hCoeffBound

/-- Helper for Theorem IV.5-extra-2: once an explicit centered product formal series agrees with the
target `tsum` on the true working ball and has radius covering that ball, the centered parametric
series is analytic at the center. -/
lemma analyticAtCenteredParametricSeries_of_workingBallOwner_local
    {m : ℕ}
    {A : ℕ → (Fin (m + 1) → ℂ) → ℂ} {x0 : Fin (m + 1) → ℂ} {u0 : ℂ}
    {r R : ℝ}
    {Q : FormalMultilinearSeries ℂ ((Fin (m + 1) → ℂ) × ℂ) ℂ}
    (hr : 0 < r) (hR : 0 < R)
    (hRadius : ENNReal.ofReal (min (r / 2) (R / 2)) ≤ Q.radius)
    (hEq :
      Set.EqOn
        (fun q : (Fin (m + 1) → ℂ) × ℂ ↦
          Q.sum (q - (x0, u0)))
        (fun q : (Fin (m + 1) → ℂ) × ℂ ↦
          ∑' n : ℕ, A n q.1 * (q.2 - u0) ^ n)
        (Metric.ball (x0, u0) (min (r / 2) (R / 2)))) :
    AnalyticAt ℂ
      (fun q : (Fin (m + 1) → ℂ) × ℂ ↦
        ∑' n : ℕ, A n q.1 * (q.2 - u0) ^ n)
      (x0, u0) := by
  have hWorkingRadiusPos : 0 < min (r / 2) (R / 2) := by
    positivity
  -- The only remaining work is to invoke the existing `EqOn`-to-`HasFPowerSeriesAt` bridge on
  -- the concrete working ball.
  exact
    (hasFPowerSeriesAtOfEqFormalSeriesOnBall_local
      (g := fun q : (Fin (m + 1) → ℂ) × ℂ ↦
        ∑' n : ℕ, A n q.1 * (q.2 - u0) ^ n)
      (P := Q) (x0 := (x0, u0)) (r := min (r / 2) (R / 2))
      hWorkingRadiusPos hRadius (by
        intro q hq
        simpa using (hEq hq).symm)).analyticAt

/-- Helper for Theorem IV.5-extra-2: the quarter-radius shrink used by the direct centered-series
pivot is still a genuine positive radius. -/
lemma shrunkWorkingRadius_pos_local
    {r R : ℝ} (hr : 0 < r) (hR : 0 < R) :
    0 < min (r / 4) (R / 4) := by
  -- Both quarter-radii stay positive, so their minimum is positive as well.
  positivity

/-- Helper for Theorem IV.5-extra-2: the quarter-radius shrink sits strictly inside the original
half-radius working ball used by the coefficient and scalar-monomial owners. -/
lemma shrunkWorkingRadius_lt_workingRadius_local
    {r R : ℝ} (hr : 0 < r) (hR : 0 < R) :
    min (r / 4) (R / 4) < min (r / 2) (R / 2) := by
  -- Compare the common quarter-radius to each half-radius separately, then take the minimum.
  refine lt_min ?_ ?_
  · have hquarter_lt : r / 4 < r / 2 := by linarith
    exact lt_of_le_of_lt (min_le_left (r / 4) (R / 4)) hquarter_lt
  · have hquarter_lt : R / 4 < R / 2 := by linarith
    exact lt_of_le_of_lt (min_le_right (r / 4) (R / 4)) hquarter_lt

/-- Helper for Theorem IV.5-extra-2: once the normalized Cauchy coefficient rows are frozen on the
common half-cylinder, the only remaining frontier is to prove analyticity of the actual normalized
`tsum` at the center directly on that consumer surface. -/
lemma normalizedProductCauchySeries_eq_explicitTransformOnSmallBall_local
    {m : ℕ}
    {D : Set ((Fin (m + 1) → ℂ) × ℂ)} {G : ((Fin (m + 1) → ℂ) × ℂ) → ℂ}
    {p : (Fin (m + 1) → ℂ) × ℂ} {ρ : ℝ}
    (hρpos : 0 < ρ)
    (hsep : ∀ q ∈ D,
      AnalyticAt ℂ (fun x : Fin (m + 1) → ℂ ↦ G (x, q.2)) q.1 ∧
        AnalyticAt ℂ (fun u : ℂ ↦ G (q.1, u)) q.2)
    (hcyl : Metric.ball p.1 (ρ / 2) ×ˢ Metric.closedBall p.2 (ρ / 2) ⊆ D) :
    Set.EqOn
      (fun q : (Fin (m + 1) → ℂ) × ℂ ↦
        ∑' n : ℕ,
          (cauchyPowerSeries (fun ζ ↦ G (q.1, ζ)) p.2 (ρ / 2)).coeff n * (q.2 - p.2) ^ n)
      (fun q : (Fin (m + 1) → ℂ) × ℂ ↦
        ((2 * Real.pi * Complex.I : ℂ)⁻¹ •
          ∮ ζ in C(p.2, ρ / 2), (ζ - q.2)⁻¹ • G (q.1, ζ)))
      (Metric.ball p (ρ / 8)) := by
  intro q hq
  have hSeriesEq :
      (∑' n : ℕ,
          (cauchyPowerSeries (fun ζ ↦ G (q.1, ζ)) p.2 (ρ / 2)).coeff n * (q.2 - p.2) ^ n) =
        G q := by
    -- The normalized local series already agrees with the original function on the smaller common
    -- ball around the center.
    exact normalizedProductCauchySeries_eqOn_smallBall_local hρpos hsep hcyl hq
  have hqdist : dist q p < ρ / 8 := by
    simpa [Metric.mem_ball] using hq
  have hprod : max (dist q.1 p.1) (dist q.2 p.2) < ρ / 8 := by
    simpa [Prod.dist_eq] using hqdist
  have heighth_lt_half : ρ / 8 < ρ / 2 := by
    linarith
  have hqBlock : q.1 ∈ Metric.ball p.1 (ρ / 2) := by
    -- The common small-ball assumption puts the block coordinate inside the original Cauchy
    -- cylinder.
    simpa [Metric.mem_ball] using lt_trans (max_lt_iff.mp hprod).1 heighth_lt_half
  have hqLast : q.2 ∈ Metric.ball p.2 (ρ / 2) := by
    -- The same small-ball assumption also keeps the last coordinate inside the interior scalar
    -- disc where the one-variable Cauchy formula applies.
    simpa [Metric.mem_ball] using lt_trans (max_lt_iff.mp hprod).2 heighth_lt_half
  have hTransformEq :
      G q =
        ((2 * Real.pi * Complex.I : ℂ)⁻¹ •
          ∮ ζ in C(p.2, ρ / 2), (ζ - q.2)⁻¹ • G (q.1, ζ)) := by
    -- Evaluate the last-variable Cauchy transform on the actual point of the working cylinder.
    exact (productLastCauchyTransform_eqOn_ball_local hsep hcyl q.1 hqBlock) hqLast
  -- Chain the two already-proved small-ball identities into the exact rewrite surface used later.
  exact hSeriesEq.trans hTransformEq

/-- Helper for Theorem IV.5-extra-2: for every point of the closed small ball, the frozen boundary
integrand is circle-integrable on the distinguished boundary circle. -/
lemma prodBoundaryIntegrand_circleIntegrable_closedSmallBall_local
    {m : ℕ}
    {D : Set ((Fin (m + 1) → ℂ) × ℂ)} {G : ((Fin (m + 1) → ℂ) × ℂ) → ℂ}
    {p : (Fin (m + 1) → ℂ) × ℂ} {ρ : ℝ}
    (hρpos : 0 < ρ)
    (hsep : ∀ q ∈ D,
      AnalyticAt ℂ (fun x : Fin (m + 1) → ℂ ↦ G (x, q.2)) q.1 ∧
        AnalyticAt ℂ (fun u : ℂ ↦ G (q.1, u)) q.2)
    (hcyl : Metric.ball p.1 (ρ / 2) ×ˢ Metric.closedBall p.2 (ρ / 2) ⊆ D) :
    ∀ q ∈ Metric.closedBall p (ρ / 8),
      CircleIntegrable (fun ζ ↦ (ζ - q.2)⁻¹ * G (q.1, ζ)) p.2 (ρ / 2) := by
  intro q hq
  have hqProd :
      max (dist q.1 p.1) (dist q.2 p.2) ≤ ρ / 8 := by
    simpa [Metric.mem_closedBall, Prod.dist_eq] using hq
  have hqBlockClosed : dist q.1 p.1 ≤ ρ / 8 := by
    exact le_trans (le_max_left _ _) hqProd
  have hqLastClosed : dist q.2 p.2 ≤ ρ / 8 := by
    exact le_trans (le_max_right _ _) hqProd
  have heighth_lt_half : ρ / 8 < ρ / 2 := by
    linarith
  have hqBlock : q.1 ∈ Metric.ball p.1 (ρ / 2) := by
    simpa [Metric.mem_ball] using lt_of_le_of_lt hqBlockClosed heighth_lt_half
  have hsliceCont :
      ContinuousOn (fun ζ ↦ G (q.1, ζ)) (Metric.sphere p.2 (ρ / 2)) := by
    refine continuousOn_of_forall_analyticAt ?_
    intro ζ hζ
    -- Restrict the last-coordinate analyticity package to the boundary circle at the frozen block
    -- point `q.1`.
    exact (hsep (q.1, ζ) (hcyl ⟨hqBlock, Metric.sphere_subset_closedBall hζ⟩)).2
  have hkernelNe :
      ∀ ζ ∈ Metric.sphere p.2 (ρ / 2), ζ - q.2 ≠ 0 := by
    intro ζ hζ hzero
    have hζdist : dist ζ p.2 = ρ / 2 := by
      simpa [Metric.mem_sphere, dist_eq_norm] using hζ
    have hEq : ζ = q.2 := sub_eq_zero.mp hzero
    have : ρ / 2 ≤ ρ / 8 := by
      calc
        ρ / 2 = dist ζ p.2 := hζdist.symm
        _ = dist q.2 p.2 := by rw [hEq]
        _ ≤ ρ / 8 := hqLastClosed
    linarith [hρpos]
  have hkernelCont :
      ContinuousOn (fun ζ : ℂ ↦ (ζ - q.2)⁻¹) (Metric.sphere p.2 (ρ / 2)) := by
    -- The boundary circle does not meet the pole `q.2`, so the inverse kernel is continuous there.
    exact ((continuous_id.continuousOn.sub continuousOn_const).inv₀ hkernelNe)
  have hIntegrandCont :
      ContinuousOn
        (fun ζ ↦ (ζ - q.2)⁻¹ * G (q.1, ζ))
        (Metric.sphere p.2 (ρ / 2)) := by
    -- Multiply the nonvanishing kernel by the continuous frozen boundary slice.
    exact hkernelCont.mul hsliceCont
  -- The boundary continuity package is exactly the circle-integrability input needed later.
  exact hIntegrandCont.circleIntegrable (by positivity)

/-- Helper for Theorem IV.5-extra-2: each frozen boundary integrand already has a concrete
power-series germ at the common center `p`. -/
lemma prodBoundaryIntegrand_hasFPowerSeriesAt_center_local
    {m : ℕ}
    {D : Set ((Fin (m + 1) → ℂ) × ℂ)} {G : ((Fin (m + 1) → ℂ) × ℂ) → ℂ}
    {p : (Fin (m + 1) → ℂ) × ℂ} {ρ : ℝ}
    (hρpos : 0 < ρ)
    (hsep : ∀ q ∈ D,
      AnalyticAt ℂ (fun x : Fin (m + 1) → ℂ ↦ G (x, q.2)) q.1 ∧
        AnalyticAt ℂ (fun u : ℂ ↦ G (q.1, u)) q.2)
    (hcyl : Metric.ball p.1 (ρ / 2) ×ˢ Metric.closedBall p.2 (ρ / 2) ⊆ D)
    {ζ : ℂ} (hζ : ζ ∈ Metric.sphere p.2 (ρ / 2)) :
    ∃ P : FormalMultilinearSeries ℂ ((Fin (m + 1) → ℂ) × ℂ) ℂ,
      HasFPowerSeriesAt
        (fun q : (Fin (m + 1) → ℂ) × ℂ ↦ (ζ - q.2)⁻¹ * G (q.1, ζ))
        P
        p := by
  have hpSmall : p ∈ Metric.ball p (ρ / 8) := by
    -- The center belongs to the common small ball on which the frozen boundary integrand is
    -- already analytic.
    simpa [Metric.mem_ball] using (show 0 < ρ / 8 by positivity)
  -- Read off the center germ from the already-closed common-ball analyticity package.
  exact
    prodBoundaryIntegrand_analyticOnNhd_commonBall_local
      (m := m) (D := D) (G := G) (p := p) (ρ := ρ) hρpos hsep hcyl hζ p hpSmall

/-- Helper for Theorem IV.5-extra-2: each frozen boundary integrand also carries some positive
ball owner at the common center, even before the radii are uniformized across the boundary circle.
-/
lemma prodBoundaryIntegrand_exists_ballOwner_center_local
    {m : ℕ}
    {D : Set ((Fin (m + 1) → ℂ) × ℂ)} {G : ((Fin (m + 1) → ℂ) × ℂ) → ℂ}
    {p : (Fin (m + 1) → ℂ) × ℂ} {ρ : ℝ}
    (hρpos : 0 < ρ)
    (hsep : ∀ q ∈ D,
      AnalyticAt ℂ (fun x : Fin (m + 1) → ℂ ↦ G (x, q.2)) q.1 ∧
        AnalyticAt ℂ (fun u : ℂ ↦ G (q.1, u)) q.2)
    (hcyl : Metric.ball p.1 (ρ / 2) ×ˢ Metric.closedBall p.2 (ρ / 2) ⊆ D)
    {ζ : ℂ} (hζ : ζ ∈ Metric.sphere p.2 (ρ / 2)) :
    ∃ P : FormalMultilinearSeries ℂ ((Fin (m + 1) → ℂ) × ℂ) ℂ,
      ∃ r : ENNReal, 0 < r ∧
        HasFPowerSeriesOnBall
          (fun q : (Fin (m + 1) → ℂ) × ℂ ↦ (ζ - q.2)⁻¹ * G (q.1, ζ))
          P
          p
          r := by
  rcases
      prodBoundaryIntegrand_hasFPowerSeriesAt_center_local
        (m := m) (D := D) (G := G) (p := p) (ρ := ρ) hρpos hsep hcyl hζ with
    ⟨P, hP⟩
  rcases hasFPowerSeriesAt_exists_ballOwner_local hP with ⟨r, hBall⟩
  -- Repackage the center germ as an honest positive-radius ball owner for later uniformization.
  exact ⟨P, r, hBall.r_pos, hBall⟩

/-- Helper for Theorem IV.5-extra-2: on the common small ball, the explicit last-variable Cauchy
transform already agrees with the normalized local `cauchyPowerSeries.sum` model. -/
lemma prodLastCauchyTransform_eq_normalizedOnSmallBall_local
    {m : ℕ}
    {D : Set ((Fin (m + 1) → ℂ) × ℂ)} {G : ((Fin (m + 1) → ℂ) × ℂ) → ℂ}
    {p : (Fin (m + 1) → ℂ) × ℂ} {ρ : ℝ}
    (hρpos : 0 < ρ)
    (hcyl : Metric.ball p.1 (ρ / 2) ×ˢ Metric.closedBall p.2 (ρ / 2) ⊆ D)
    (hsep : ∀ q ∈ D,
      AnalyticAt ℂ (fun x : Fin (m + 1) → ℂ ↦ G (x, q.2)) q.1 ∧
        AnalyticAt ℂ (fun u : ℂ ↦ G (q.1, u)) q.2) :
    ∀ q ∈ Metric.ball p (ρ / 8),
      ((2 * Real.pi * Complex.I : ℂ)⁻¹ •
        ∮ ζ in C(p.2, ρ / 2), (ζ - q.2)⁻¹ • G (q.1, ζ)) =
      (cauchyPowerSeries (fun ζ ↦ G (q.1, ζ)) p.2 (ρ / 2)).sum (q.2 - p.2) := by
  intro q hq
  have hEqOn :=
    normalizedProductCauchySeries_eq_explicitTransformOnSmallBall_local
      (m := m) (D := D) (G := G) (p := p) (ρ := ρ) hρpos hsep hcyl
  have hTsumEq :
      (cauchyPowerSeries (fun ζ ↦ G (q.1, ζ)) p.2 (ρ / 2)).sum (q.2 - p.2) =
        ∑' n : ℕ,
          (cauchyPowerSeries (fun ζ ↦ G (q.1, ζ)) p.2 (ρ / 2)).coeff n * (q.2 - p.2) ^ n := by
    -- Rewrite the normalized local `sum` once into its coefficient `tsum` form.
    simpa using cauchyPowerSeries_sum_eq_tsum_coeff
  -- The small-ball identity to the explicit integral and the coefficient expansion of
  -- `cauchyPowerSeries.sum` are the only normalizations needed by the downstream support theorem.
  exact (hEqOn hq).symm.trans hTsumEq.symm

/-- Helper for Theorem IV.5-extra-2: every frozen block point on the inner ball already gives a
last-variable analytic owner on the whole closed disc cut out by the product cylinder. -/
lemma productLastSlices_analyticOnNhd_closedBall_local
    {m : ℕ}
    {D : Set ((Fin (m + 1) → ℂ) × ℂ)} {G : ((Fin (m + 1) → ℂ) × ℂ) → ℂ}
    {p : ((Fin (m + 1) → ℂ) × ℂ)} {r R : ℝ}
    (hsep : ∀ q ∈ D,
      AnalyticAt ℂ (fun x : Fin (m + 1) → ℂ ↦ G (x, q.2)) q.1 ∧
        AnalyticAt ℂ (fun u : ℂ ↦ G (q.1, u)) q.2)
    (hcyl : Metric.ball p.1 r ×ˢ Metric.closedBall p.2 R ⊆ D)
    (x : Fin (m + 1) → ℂ) (hx : x ∈ Metric.ball p.1 r) :
    AnalyticOnNhd ℂ (fun w ↦ G (x, w)) (Metric.closedBall p.2 R) := by
  intro w hw
  -- The closed last-variable disc stays inside the ambient cylinder, so the separate analyticity
  -- hypothesis can be read off directly at each frozen point `(x, w)`.
  exact (hsep (x, w) (hcyl ⟨hx, hw⟩)).2

/-- Helper for Theorem IV.5-extra-2: every normalized last-variable Cauchy coefficient row already
has a pointwise geometric Cauchy bound on the inner block ball. The only missing step afterward is
to uniformize these pointwise constants on the compact closed small ball. -/
lemma normalizedProductCauchyCoeffPointwiseBound_local
    {m : ℕ}
    {D : Set ((Fin (m + 1) → ℂ) × ℂ)} {G : ((Fin (m + 1) → ℂ) × ℂ) → ℂ}
    {p : ((Fin (m + 1) → ℂ) × ℂ)} {ρ : ℝ}
    (hρpos : 0 < ρ)
    (hcyl : Metric.ball p.1 (ρ / 2) ×ˢ Metric.closedBall p.2 (ρ / 2) ⊆ D)
    (hsep : ∀ q ∈ D,
      AnalyticAt ℂ (fun x : Fin (m + 1) → ℂ ↦ G (x, q.2)) q.1 ∧
        AnalyticAt ℂ (fun u : ℂ ↦ G (q.1, u)) q.2) :
    let w0 : ℂ := p.2
    let r0 : ℝ := ρ / 8
    let A : ℕ → (Fin (m + 1) → ℂ) → ℂ := fun n x ↦
      (cauchyPowerSeries (fun ζ ↦ G (x, ζ)) w0 (ρ / 2)).coeff n
    ∀ x ∈ Metric.ball p.1 r0,
      ∃ Cx : ℝ, 0 ≤ Cx ∧
        ∀ n : ℕ, ‖A n x‖ ≤ Cx / (ρ / 2 : ℝ) ^ n := by
  let w0 : ℂ := p.2
  let r0 : ℝ := ρ / 8
  let A : ℕ → (Fin (m + 1) → ℂ) → ℂ := fun n x ↦
    (cauchyPowerSeries (fun ζ ↦ G (x, ζ)) w0 (ρ / 2)).coeff n
  -- Prove the pointwise scalar estimate on the explicit coefficient surface first, then fold it
  -- back into the frozen notation `w0`, `r0`, and `A`.
  simpa [w0, r0, A] using
    (show
      ∀ x ∈ Metric.ball p.1 (ρ / 8),
        ∃ Cx : ℝ, 0 ≤ Cx ∧
          ∀ n : ℕ,
            ‖(cauchyPowerSeries (fun ζ ↦ G (x, ζ)) p.2 (ρ / 2)).coeff n‖ ≤
              Cx / (ρ / 2 : ℝ) ^ n from by
      intro x hx
      have hr0_lt_half : r0 < ρ / 2 := by
        dsimp [r0]
        linarith
      have hcylSmall :
          Metric.ball p.1 r0 ×ˢ Metric.closedBall w0 (ρ / 2) ⊆ D := by
        intro q hq
        exact hcyl ⟨Metric.ball_subset_ball (le_of_lt hr0_lt_half) hq.1, hq.2⟩
      have hSliceOn :
          AnalyticOnNhd ℂ (fun w ↦ G (x, w)) (Metric.closedBall w0 (ρ / 2)) := by
        -- Freeze the block point `x` and read the last-variable analyticity straight from the ambient
        -- cylinder.
        exact
          productLastSlices_analyticOnNhd_closedBall_local
            (m := m) (D := D) (G := G) (p := p) (r := r0) (R := ρ / 2)
            hsep hcylSmall x hx
      let Rlast : NNReal := ⟨ρ / 2, by linarith [hρpos]⟩
      have hRlastPos : 0 < Rlast := by
        exact_mod_cast (show 0 < ρ / 2 by positivity)
      obtain ⟨Cx, hCxnonneg, hCx⟩ :=
        cauchyPowerSeries_coeff_norm_le_div_pow_of_continuousOn_closedBall
          (u0 := w0) (R := Rlast) (F := fun w ↦ G (x, w)) hRlastPos hSliceOn.continuousOn
      refine ⟨Cx, hCxnonneg, ?_⟩
      intro n
      -- Re-express the scalar Cauchy estimate in the local coefficient notation.
      simpa [Rlast] using hCx n)

/-- Helper for Theorem IV.5-extra-2: the compact torus needed by the global coefficient package is
the smaller surface `Metric.closedBall p.1 ((ρ / 8) / 2) ×ˢ Metric.sphere p.2 (ρ / 2)`, not the
larger ambient cylinder. -/
lemma prodBoundaryJointContinuousOnClosedSmallBallSphere_fromProdHartogs_local
    {m : ℕ}
    (prodHartogs :
      ∀ {D : Set ((Fin (m + 1) → ℂ) × ℂ)} {G : ((Fin (m + 1) → ℂ) × ℂ) → ℂ},
        IsOpen D →
        (∀ p ∈ D,
          AnalyticAt ℂ (fun x : Fin (m + 1) → ℂ ↦ G (x, p.2)) p.1 ∧
            AnalyticAt ℂ (fun u : ℂ ↦ G (p.1, u)) p.2) →
        AnalyticOnNhd ℂ G D)
    {D : Set ((Fin (m + 1) → ℂ) × ℂ)} {G : ((Fin (m + 1) → ℂ) × ℂ) → ℂ}
    {p : (Fin (m + 1) → ℂ) × ℂ} {ρ : ℝ}
    (hD : IsOpen D)
    (hρpos : 0 < ρ)
    (hcyl : Metric.ball p.1 (ρ / 2) ×ˢ Metric.closedBall p.2 (ρ / 2) ⊆ D)
    (hsep : ∀ q ∈ D,
      AnalyticAt ℂ (fun x : Fin (m + 1) → ℂ ↦ G (x, q.2)) q.1 ∧
        AnalyticAt ℂ (fun u : ℂ ↦ G (q.1, u)) q.2) :
    ContinuousOn
      (Function.uncurry fun x ζ ↦ G (x, ζ))
      (Metric.closedBall p.1 ((ρ / 8) / 2) ×ˢ Metric.sphere p.2 (ρ / 2)) := by
  -- The compact torus continuity is obtained pointwise from a genuinely open product
  -- neighborhood, then upgraded by `continuousOn_of_forall_analyticAt`.
  refine continuousOn_of_forall_analyticAt ?_
  intro q hq
  have hqBlock : q.1 ∈ Metric.ball p.1 (ρ / 2) := by
    have hsmall : (ρ / 8) / 2 < ρ / 2 := by
      linarith
    exact Metric.closedBall_subset_ball hsmall hq.1
  have hqD : q ∈ D := hcyl ⟨hqBlock, Metric.sphere_subset_closedBall hq.2⟩
  obtain ⟨δ, hδpos, hδsub⟩ := exists_productCylinder_subset_of_isOpen_local hD hqD
  let Dloc : Set ((Fin (m + 1) → ℂ) × ℂ) := Metric.ball q.1 (δ / 2) ×ˢ Metric.ball q.2 (δ / 2)
  have hDlocOpen : IsOpen Dloc := Metric.isOpen_ball.prod Metric.isOpen_ball
  have hDlocSub : Dloc ⊆ D := by
    intro r hr
    exact hδsub ⟨hr.1, Metric.ball_subset_closedBall hr.2⟩
  have hGOn : AnalyticOnNhd ℂ G Dloc := by
    refine prodHartogs hDlocOpen ?_
    intro r hr
    exact hsep r (hDlocSub hr)
  have hqLoc : q ∈ Dloc := by
    refine ⟨?_, ?_⟩
    · simpa [Metric.mem_ball] using (show 0 < δ / 2 by positivity)
    · simpa [Metric.mem_ball] using (show 0 < δ / 2 by positivity)
  -- Evaluate the local Hartogs owner at the actual torus point.
  simpa [Function.uncurry] using hGOn q hqLoc

/-- Helper for Theorem IV.5-extra-2: once the earlier centered parametric-series callback is
available, the specialized normalized Cauchy series is only a direct coefficient-package
instantiation. -/
lemma centeredParametricSeries_analyticAt_fromCoeffBoundPackage_local
    {m : ℕ}
    (parametricUniform :
      ∀ {A : ℕ → (Fin (m + 1) → ℂ) → ℂ} {x0 : Fin (m + 1) → ℂ} {u0 : ℂ}
        {r R C : ℝ},
        0 < r →
        0 < R →
        (∀ n : ℕ, AnalyticOnNhd ℂ (A n) (Metric.ball x0 r)) →
        (∀ x ∈ Metric.closedBall x0 (r / 2), ∀ n : ℕ, ‖A n x‖ ≤ C / R ^ n) →
        AnalyticAt ℂ
          (fun q : (Fin (m + 1) → ℂ) × ℂ ↦
            ∑' n : ℕ, A n q.1 * (q.2 - u0) ^ n)
          (x0, u0))
    {A : ℕ → (Fin (m + 1) → ℂ) → ℂ} {x0 : Fin (m + 1) → ℂ} {u0 : ℂ}
    {r R : ℝ}
    (hr : 0 < r)
    (hR : 0 < R)
    (hCoeffOn : ∀ n : ℕ, AnalyticOnNhd ℂ (A n) (Metric.ball x0 r))
    (hCoeffBound :
      ∃ C : ℝ, 0 ≤ C ∧
        ∀ x ∈ Metric.closedBall x0 (r / 2), ∀ n : ℕ, ‖A n x‖ ≤ C / R ^ n) :
    AnalyticAt ℂ
      (fun q : (Fin (m + 1) → ℂ) × ℂ ↦
        ∑' n : ℕ, A n q.1 * (q.2 - u0) ^ n)
      (x0, u0) := by
  rcases hCoeffBound with ⟨C, hCnonneg, hCbound⟩
  have hCbound' :
      ∀ x ∈ Metric.closedBall x0 (r / 2), ∀ n : ℕ, ‖A n x‖ ≤ C / R ^ n := by
    intro x hx n
    exact hCbound x hx n
  -- The coefficient package already isolates one global geometric majorant, so the support theorem
  -- closes the germ immediately.
  exact parametricUniform hr hR hCoeffOn hCbound'

/-- Helper for Theorem IV.5-extra-2: the compact torus needed by the global coefficient package is
the smaller surface `Metric.closedBall p.1 ((ρ / 8) / 2) ×ˢ Metric.sphere p.2 (ρ / 2)`, not the
larger ambient cylinder. -/
lemma prodBoundaryJointContinuousOnClosedSmallBallSphere_local
    {m : ℕ}
    (ih : ∀ {D' : Set (Fin (m + 1) → ℂ)} {f' : (Fin (m + 1) → ℂ) → ℂ},
      IsOpen D' →
      (∀ z ∈ D', ∀ i : Fin (m + 1), AnalyticAt ℂ (fun w ↦ f' (Function.update z i w)) (z i)) →
      AnalyticOnNhd ℂ f' D')
    {D : Set ((Fin (m + 1) → ℂ) × ℂ)} {G : ((Fin (m + 1) → ℂ) × ℂ) → ℂ}
    {p : (Fin (m + 1) → ℂ) × ℂ} {ρ : ℝ}
    (hD : IsOpen D)
    (hρpos : 0 < ρ)
    (hcyl : Metric.ball p.1 (ρ / 2) ×ˢ Metric.closedBall p.2 (ρ / 2) ⊆ D)
    (hsep : ∀ q ∈ D,
      AnalyticAt ℂ (fun x : Fin (m + 1) → ℂ ↦ G (x, q.2)) q.1 ∧
        AnalyticAt ℂ (fun u : ℂ ↦ G (q.1, u)) q.2) :
    ContinuousOn
      (Function.uncurry fun x ζ ↦ G (x, ζ))
      (Metric.closedBall p.1 ((ρ / 8) / 2) ×ˢ Metric.sphere p.2 (ρ / 2)) := by
  -- Route correction: this compact-torus continuity theorem is only a consumer of the single
  -- product-Hartogs frontier isolated above, so keep it as a thin restriction wrapper.
  exact
    prodBoundaryJointContinuousOnClosedSmallBallSphere_fromProdHartogs_local
      (prodHartogs := fun hDprod hsepProd ↦
        separatelyHolomorphicProd_analyticOnNhd_base_local
          (m := m) ih hDprod hsepProd)
      hD hρpos hcyl hsep

/-- Helper for Theorem IV.5-extra-2: once the noncircular product Hartogs callback is available,
the compact torus continuity statement is only a local product-neighborhood restriction around each
torus point. -/
lemma prodBoundaryJointContinuousOnClosedSmallBallSphere_ofProdHartogs_local
    {m : ℕ}
    (prodHartogs :
      ∀ {D : Set ((Fin (m + 1) → ℂ) × ℂ)} {G : ((Fin (m + 1) → ℂ) × ℂ) → ℂ},
        IsOpen D →
        (∀ p ∈ D,
          AnalyticAt ℂ (fun x : Fin (m + 1) → ℂ ↦ G (x, p.2)) p.1 ∧
            AnalyticAt ℂ (fun u : ℂ ↦ G (p.1, u)) p.2) →
        AnalyticOnNhd ℂ G D)
    {D : Set ((Fin (m + 1) → ℂ) × ℂ)} {G : ((Fin (m + 1) → ℂ) × ℂ) → ℂ}
    {p : (Fin (m + 1) → ℂ) × ℂ} {ρ : ℝ}
    (hD : IsOpen D)
    (hρpos : 0 < ρ)
    (hcyl : Metric.ball p.1 (ρ / 2) ×ˢ Metric.closedBall p.2 (ρ / 2) ⊆ D)
    (hsep : ∀ q ∈ D,
      AnalyticAt ℂ (fun x : Fin (m + 1) → ℂ ↦ G (x, q.2)) q.1 ∧
        AnalyticAt ℂ (fun u : ℂ ↦ G (q.1, u)) q.2) :
    ContinuousOn
      (Function.uncurry fun x ζ ↦ G (x, ζ))
      (Metric.closedBall p.1 ((ρ / 8) / 2) ×ˢ Metric.sphere p.2 (ρ / 2)) := by
  -- The compact torus continuity is obtained pointwise from a genuinely open product
  -- neighborhood, then upgraded by `continuousOn_of_forall_analyticAt`.
  refine continuousOn_of_forall_analyticAt ?_
  intro q hq
  have hqBlock : q.1 ∈ Metric.ball p.1 (ρ / 2) := by
    have hsmall : (ρ / 8) / 2 < ρ / 2 := by
      linarith
    exact Metric.closedBall_subset_ball hsmall hq.1
  have hqD : q ∈ D := hcyl ⟨hqBlock, Metric.sphere_subset_closedBall hq.2⟩
  obtain ⟨δ, hδpos, hδsub⟩ := exists_productCylinder_subset_of_isOpen_local hD hqD
  let Dloc : Set ((Fin (m + 1) → ℂ) × ℂ) := Metric.ball q.1 (δ / 2) ×ˢ Metric.ball q.2 (δ / 2)
  have hDlocOpen : IsOpen Dloc := Metric.isOpen_ball.prod Metric.isOpen_ball
  have hDlocSub : Dloc ⊆ D := by
    intro r hr
    exact hδsub ⟨hr.1, Metric.ball_subset_closedBall hr.2⟩
  have hGOn : AnalyticOnNhd ℂ G Dloc := by
    refine prodHartogs hDlocOpen ?_
    intro r hr
    exact hsep r (hDlocSub hr)
  have hqLoc : q ∈ Dloc := by
    refine ⟨?_, ?_⟩
    · simpa [Metric.mem_ball] using (show 0 < δ / 2 by positivity)
    · simpa [Metric.mem_ball] using (show 0 < δ / 2 by positivity)
  -- Evaluate the local Hartogs owner at the actual torus point.
  simpa [Function.uncurry] using hGOn q hqLoc

/-- Helper for Theorem IV.5-extra-2: once the smaller compact torus continuity surface is
available, the generic closed-ball Cauchy estimate immediately yields one global geometric bound
for all normalized coefficient rows on the same smaller closed block ball. -/
lemma normalizedProductCauchyCoeffUniformBound_local
    {m : ℕ}
    (ih : ∀ {D' : Set (Fin (m + 1) → ℂ)} {f' : (Fin (m + 1) → ℂ) → ℂ},
      IsOpen D' →
      (∀ z ∈ D', ∀ i : Fin (m + 1), AnalyticAt ℂ (fun w ↦ f' (Function.update z i w)) (z i)) →
      AnalyticOnNhd ℂ f' D')
    {D : Set ((Fin (m + 1) → ℂ) × ℂ)} {G : ((Fin (m + 1) → ℂ) × ℂ) → ℂ}
    {p : (Fin (m + 1) → ℂ) × ℂ} {ρ : ℝ}
    (hD : IsOpen D)
    (hρpos : 0 < ρ)
    (hcyl : Metric.ball p.1 (ρ / 2) ×ˢ Metric.closedBall p.2 (ρ / 2) ⊆ D)
    (hsep : ∀ q ∈ D,
      AnalyticAt ℂ (fun x : Fin (m + 1) → ℂ ↦ G (x, q.2)) q.1 ∧
        AnalyticAt ℂ (fun u : ℂ ↦ G (q.1, u)) q.2) :
    let w0 : ℂ := p.2
    let r0 : ℝ := ρ / 8
    let r1 : ℝ := r0 / 2
    let A : ℕ → (Fin (m + 1) → ℂ) → ℂ := fun n x ↦
      (cauchyPowerSeries (fun ζ ↦ G (x, ζ)) w0 (ρ / 2)).coeff n
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ x ∈ Metric.closedBall p.1 r1, ∀ n : ℕ, ‖A n x‖ ≤ C / (ρ / 2 : ℝ) ^ n := by
  let w0 : ℂ := p.2
  let r0 : ℝ := ρ / 8
  let r1 : ℝ := r0 / 2
  let A : ℕ → (Fin (m + 1) → ℂ) → ℂ := fun n x ↦
    (cauchyPowerSeries (fun ζ ↦ G (x, ζ)) w0 (ρ / 2)).coeff n
  have hcont :
      ContinuousOn
        (Function.uncurry fun x ζ ↦ G (x, ζ))
        (Metric.closedBall p.1 r1 ×ˢ Metric.sphere w0 (ρ / 2)) := by
    -- Consume the compact-torus continuity theorem in the exact radius normal form used by the
    -- generic closed-ball coefficient estimate.
    simpa [w0, r0, r1] using
      prodBoundaryJointContinuousOnClosedSmallBallSphere_local
        (m := m) ih (D := D) (G := G) (p := p) (ρ := ρ) hD hρpos hcyl hsep
  obtain ⟨C, hCnonneg, hCbound⟩ :=
    cauchyPowerSeries_coeff_uniformBound_of_continuousOn_closedBall
      (x0 := p.1) (r := r1) (u0 := w0) (R := ρ / 2)
      (F := fun x ζ ↦ G (x, ζ)) (by positivity) hcont
  refine ⟨C, hCnonneg, ?_⟩
  intro x hx n
  -- Re-express the generic compact-torus coefficient package in the frozen local notation `A`.
  simpa [A, w0] using hCbound x hx n

/-- Helper for Theorem IV.5-extra-2: separate analyticity in product coordinates should upgrade to
joint analyticity on the same open product domain without calling back into the recursive local
normalized-series closeout. -/
lemma normalizedProductCauchySeries_analyticAt_center_specialized_local
    {m : ℕ}
    (ih : ∀ {D' : Set (Fin (m + 1) → ℂ)} {f' : (Fin (m + 1) → ℂ) → ℂ},
      IsOpen D' →
      (∀ z ∈ D', ∀ i : Fin (m + 1), AnalyticAt ℂ (fun w ↦ f' (Function.update z i w)) (z i)) →
      AnalyticOnNhd ℂ f' D')
    {D : Set ((Fin (m + 1) → ℂ) × ℂ)} {G : ((Fin (m + 1) → ℂ) × ℂ) → ℂ}
    {p : (Fin (m + 1) → ℂ) × ℂ} {ρ : ℝ}
    (hD : IsOpen D)
    (hρpos : 0 < ρ)
    (hcyl : Metric.ball p.1 (ρ / 2) ×ˢ Metric.closedBall p.2 (ρ / 2) ⊆ D)
    (hsep : ∀ q ∈ D,
      AnalyticAt ℂ (fun x : Fin (m + 1) → ℂ ↦ G (x, q.2)) q.1 ∧
        AnalyticAt ℂ (fun u : ℂ ↦ G (q.1, u)) q.2) :
    AnalyticAt ℂ
      (fun q : (Fin (m + 1) → ℂ) × ℂ ↦
        ∑' n : ℕ,
          (cauchyPowerSeries (fun ζ ↦ G (q.1, ζ)) p.2 (ρ / 2)).coeff n * (q.2 - p.2) ^ n)
      p := by
  -- Keep the later legacy wrapper as a thin alias of the earlier dedicated center-germ helper.
  exact
    normalizedProductCauchySeries_analyticAt_center_direct_local
      (m := m) ih (D := D) (G := G) (p := p) (ρ := ρ) hD hρpos hcyl hsep

/-- Helper for Theorem IV.5-extra-2: once the earlier centered parametric-series callback is
available, the specialized normalized Cauchy series is only a direct coefficient-package
instantiation. -/
lemma centeredParametricSeries_analyticAt_ofCoeffBoundPackage_local
    {m : ℕ}
    (parametricUniform :
      ∀ {A : ℕ → (Fin (m + 1) → ℂ) → ℂ} {x0 : Fin (m + 1) → ℂ} {u0 : ℂ}
        {r R C : ℝ},
        0 < r →
        0 < R →
        (∀ n : ℕ, AnalyticOnNhd ℂ (A n) (Metric.ball x0 r)) →
        (∀ x ∈ Metric.closedBall x0 (r / 2), ∀ n : ℕ, ‖A n x‖ ≤ C / R ^ n) →
        AnalyticAt ℂ
          (fun q : (Fin (m + 1) → ℂ) × ℂ ↦
            ∑' n : ℕ, A n q.1 * (q.2 - u0) ^ n)
          (x0, u0))
    {A : ℕ → (Fin (m + 1) → ℂ) → ℂ} {x0 : Fin (m + 1) → ℂ} {u0 : ℂ}
    {r R : ℝ}
    (hr : 0 < r) (hR : 0 < R)
    (hCoeffOn : ∀ n : ℕ, AnalyticOnNhd ℂ (A n) (Metric.ball x0 r))
    (hCoeffBound :
      ∃ C : ℝ, 0 ≤ C ∧
        ∀ x ∈ Metric.closedBall x0 (r / 2), ∀ n : ℕ, ‖A n x‖ ≤ C / R ^ n) :
    AnalyticAt ℂ
      (fun q : (Fin (m + 1) → ℂ) × ℂ ↦
        ∑' n : ℕ, A n q.1 * (q.2 - u0) ^ n)
      (x0, u0) := by
  rcases hCoeffBound with ⟨C, _hCnonneg, hCbound⟩
  -- Once the coefficient bound is uniformized into one constant, the centered-series callback
  -- closes the germ immediately.
  exact parametricUniform hr hR hCoeffOn hCbound

lemma separatelyHolomorphicProd_analyticOnNhd_independent_local
    {m : ℕ}
    (ih : ∀ {D' : Set (Fin (m + 1) → ℂ)} {f' : (Fin (m + 1) → ℂ) → ℂ},
      IsOpen D' →
      (∀ z ∈ D', ∀ i : Fin (m + 1), AnalyticAt ℂ (fun w ↦ f' (Function.update z i w)) (z i)) →
      AnalyticOnNhd ℂ f' D')
    {D : Set ((Fin (m + 1) → ℂ) × ℂ)} {G : ((Fin (m + 1) → ℂ) × ℂ) → ℂ}
    (hD : IsOpen D)
    (hsep : ∀ p ∈ D,
      AnalyticAt ℂ (fun w : Fin (m + 1) → ℂ ↦ G (w, p.2)) p.1 ∧
        AnalyticAt ℂ (fun w ↦ G (p.1, w)) p.2) :
    AnalyticOnNhd ℂ G D := by
  -- The earlier base callback is now the canonical owner for this exact statement surface.
  exact separatelyHolomorphicProd_analyticOnNhd_base_local (m := m) ih hD hsep

/-- Helper for Theorem IV.5-extra-2: the centered parametric power series with a common geometric
coefficient bound should close directly at the center, without routing back through the later local
product-Hartogs theorem. -/
lemma analyticAtCenteredParametricSeriesOfUniformCoeffBoundDirect_local
    {m : ℕ}
    (ih : ∀ {D' : Set (Fin (m + 1) → ℂ)} {f' : (Fin (m + 1) → ℂ) → ℂ},
      IsOpen D' →
      (∀ z ∈ D', ∀ i : Fin (m + 1), AnalyticAt ℂ (fun w ↦ f' (Function.update z i w)) (z i)) →
      AnalyticOnNhd ℂ f' D')
    {A : ℕ → (Fin (m + 1) → ℂ) → ℂ} {x0 : Fin (m + 1) → ℂ} {u0 : ℂ}
    {r R C : ℝ}
    (hr : 0 < r) (hR : 0 < R)
    (hCoeffOn : ∀ n : ℕ, AnalyticOnNhd ℂ (A n) (Metric.ball x0 r))
    (hCoeffBound : ∀ x ∈ Metric.closedBall x0 (r / 2), ∀ n : ℕ, ‖A n x‖ ≤ C / R ^ n) :
    AnalyticAt ℂ
      (fun p : (Fin (m + 1) → ℂ) × ℂ ↦
        ∑' n : ℕ, A n p.1 * (p.2 - u0) ^ n)
      (x0, u0) := by
  -- Route correction: consume the support theorem through the single earlier product-Hartogs
  -- frontier, rather than routing back through the later recursive wrapper.
  exact
    analyticAt_parametricPowerSeries_of_uniformCoeffBound_of_prodHartogs_local
      (prodHartogs := fun hD hsep ↦
        separatelyHolomorphicProd_analyticOnNhd_base_local
          (m := m) ih hD hsep)
      ih hr hR hCoeffOn hCoeffBound

/-- Helper for Theorem IV.5-extra-2: separate analyticity in the block and last coordinates is
enough to recover joint analyticity on the product domain, via the normalized local Cauchy
series. -/
lemma separatelyHolomorphicProd_analyticOnNhd_local
    {m : ℕ}
    (ih : ∀ {D' : Set (Fin (m + 1) → ℂ)} {f' : (Fin (m + 1) → ℂ) → ℂ},
      IsOpen D' →
      (∀ z ∈ D', ∀ i : Fin (m + 1), AnalyticAt ℂ (fun w ↦ f' (Function.update z i w)) (z i)) →
      AnalyticOnNhd ℂ f' D')
    {D : Set ((Fin (m + 1) → ℂ) × ℂ)} {G : ((Fin (m + 1) → ℂ) × ℂ) → ℂ}
    (hD : IsOpen D)
    (hsep : ∀ p ∈ D,
      AnalyticAt ℂ (fun w : Fin (m + 1) → ℂ ↦ G (w, p.2)) p.1 ∧
        AnalyticAt ℂ (fun w ↦ G (p.1, w)) p.2) :
    AnalyticOnNhd ℂ G D := by
  -- The direct product-domain closeout above already proves the same theorem on this exact
  -- statement surface, so keep the legacy wrapper as a thin alias.
  exact separatelyHolomorphicProd_analyticOnNhd_independent_local (m := m) ih hD hsep

/-- Helper for Theorem IV.5-extra-2: once the `Fin 1 × ℂ` product Hartogs owner is supplied
explicitly, the `Fin 2` case is only the coordinate pack/unpack transport. -/
lemma separatelyHolomorphicFin2_ofProdHartogs_local
    (prodHartogs :
      ∀ {D : Set ((Fin 1 → ℂ) × ℂ)} {G : ((Fin 1 → ℂ) × ℂ) → ℂ},
        IsOpen D →
        (∀ p ∈ D,
          AnalyticAt ℂ (fun w : Fin 1 → ℂ ↦ G (w, p.2)) p.1 ∧
            AnalyticAt ℂ (fun w ↦ G (p.1, w)) p.2) →
        AnalyticOnNhd ℂ G D)
    {D2 : Set (Fin 2 → ℂ)} {F : (Fin 2 → ℂ) → ℂ}
    (hD2 : IsOpen D2)
    (hsep2 :
      ∀ z ∈ D2, ∀ i : Fin 2, AnalyticAt ℂ (fun w ↦ F (Function.update z i w)) (z i)) :
    AnalyticOnNhd ℂ F D2 := by
  intro z hz
  let pack : (Fin 1 → ℂ) × ℂ → Fin 2 → ℂ := fun p ↦ ![p.1 0, p.2]
  let unpack : (Fin 2 → ℂ) → (Fin 1 → ℂ) × ℂ := fun w ↦ ((fun _ : Fin 1 ↦ w 0), w 1)
  let G : ((Fin 1 → ℂ) × ℂ) → ℂ := F ∘ pack
  let D : Set ((Fin 1 → ℂ) × ℂ) := pack ⁻¹' D2
  have hPackCont : Continuous pack := by
    refine continuous_pi fun i ↦ ?_
    fin_cases i
    · simpa [pack] using
        (continuous_apply 0).comp
          (continuous_fst : Continuous fun p : (Fin 1 → ℂ) × ℂ ↦ p.1)
    · simpa [pack] using (continuous_snd : Continuous fun p : (Fin 1 → ℂ) × ℂ ↦ p.2)
  have hD : IsOpen D := hD2.preimage hPackCont
  have hPackUnpack : ∀ w : Fin 2 → ℂ, pack (unpack w) = w := by
    intro w
    ext i
    fin_cases i <;> simp [pack, unpack]
  have hzD : unpack z ∈ D := by
    change pack (unpack z) ∈ D2
    simpa [hPackUnpack z] using hz
  have hsepProd :
      ∀ p ∈ D,
        AnalyticAt ℂ (fun w : Fin 1 → ℂ ↦ G (w, p.2)) p.1 ∧
          AnalyticAt ℂ (fun w ↦ G (p.1, w)) p.2 := by
    intro p hp
    have hp' : pack p ∈ D2 := hp
    constructor
    · have hslice :
          AnalyticAt ℂ (fun w ↦ F (Function.update (pack p) 0 w)) ((pack p) 0) :=
        hsep2 (pack p) hp' 0
      let proj0 : (Fin 1 → ℂ) →L[ℂ] ℂ := ContinuousLinearMap.proj 0
      have hEval : AnalyticAt ℂ (fun w : Fin 1 → ℂ ↦ w 0) p.1 := by
        simpa using
          (ContinuousLinearMap.analyticAt proj0 p.1)
      have hComp :
          AnalyticAt ℂ (fun w : Fin 1 → ℂ ↦ F (Function.update (pack p) 0 (w 0))) p.1 := by
        have hCenter : (fun w : Fin 1 → ℂ ↦ w 0) p.1 = (pack p) 0 := rfl
        simpa [pack] using hslice.comp_of_eq hEval hCenter
      have hArgEq :
          ∀ w : Fin 1 → ℂ, pack (w, p.2) = Function.update (pack p) 0 (w 0) := by
        intro w
        ext i
        fin_cases i <;> simp [pack, Function.update]
      have hEq :
          (fun w : Fin 1 → ℂ ↦ G (w, p.2)) =
            (fun w : Fin 1 → ℂ ↦ F (Function.update (pack p) 0 (w 0))) := by
        funext w
        simp [G, hArgEq w]
      simpa [hEq] using hComp
    · have hslice :
          AnalyticAt ℂ (fun w ↦ F (Function.update (pack p) 1 w)) ((pack p) 1) :=
        hsep2 (pack p) hp' 1
      have hArgEq : ∀ w : ℂ, pack (p.1, w) = Function.update (pack p) 1 w := by
        intro w
        ext i
        fin_cases i <;> simp [pack, Function.update]
      have hEq :
          (fun w : ℂ ↦ G (p.1, w)) = (fun w : ℂ ↦ F (Function.update (pack p) 1 w)) := by
        funext w
        simp [G, hArgEq w]
      simpa [hEq] using hslice
  have hGOn : AnalyticOnNhd ℂ G D := prodHartogs hD hsepProd
  have hGAt : AnalyticAt ℂ G (unpack z) := hGOn (unpack z) hzD
  have hUnpackAt : AnalyticAt ℂ unpack z := by
    have hFirst :
        AnalyticAt ℂ (fun w : Fin 2 → ℂ ↦ fun _ : Fin 1 ↦ w 0) z := by
      let proj0 : (Fin 2 → ℂ) →L[ℂ] ℂ := ContinuousLinearMap.proj 0
      refine AnalyticAt.pi fun i ↦ ?_
      fin_cases i
      simpa using
        (ContinuousLinearMap.analyticAt proj0 z)
    have hSecond : AnalyticAt ℂ (fun w : Fin 2 → ℂ ↦ w 1) z := by
      let proj1 : (Fin 2 → ℂ) →L[ℂ] ℂ := ContinuousLinearMap.proj 1
      simpa using
        (ContinuousLinearMap.analyticAt proj1 z)
    simpa [unpack] using hFirst.prod hSecond
  have hEq : (fun w : Fin 2 → ℂ ↦ G (unpack w)) = F := by
    funext w
    simp [G, unpack, hPackUnpack w]
  have hFGerm : AnalyticAt ℂ (fun w : Fin 2 → ℂ ↦ G (unpack w)) z := by
    simpa using hGAt.comp hUnpackAt
  simpa [hEq] using hFGerm

/-- Helper for Theorem IV.5-extra-2: the `Fin 2` base case is the support-file owner specialized
to the local product Hartogs callback above. -/
lemma separatelyHolomorphicFin2_analyticOnNhd_independent_local
    {D2 : Set (Fin 2 → ℂ)} {F : (Fin 2 → ℂ) → ℂ}
    (hD2 : IsOpen D2)
    (hsep2 :
      ∀ z ∈ D2, ∀ i : Fin 2, AnalyticAt ℂ (fun w ↦ F (Function.update z i w)) (z i)) :
    AnalyticOnNhd ℂ F D2 := by
  have ih1 :
      ∀ {D' : Set (Fin 1 → ℂ)} {f' : (Fin 1 → ℂ) → ℂ},
        IsOpen D' →
        (∀ z ∈ D', ∀ i : Fin 1, AnalyticAt ℂ (fun w ↦ f' (Function.update z i w)) (z i)) →
        AnalyticOnNhd ℂ f' D' := by
    intro D' f' _ hsep'
    -- In one variable the unique slice is the whole function.
    exact separatelyHolomorphicSingleton_analyticOnNhd hsep'
  -- Route correction: consume the dedicated `Fin 2` support owner rather than reviving the older
  -- local bidisc reconstruction.
  simpa using
    separatelyHolomorphicFin2_ofProdHartogs_local
      (fun hD hsep ↦ separatelyHolomorphicProd_analyticOnNhd_local ih1 hD hsep)
      hD2 hsep2

/-- Helper for Theorem IV.5-extra-2: the support-level parametric power-series closeout only needs
the local product Hartogs callback specialized once. -/
lemma analyticAtParametricPowerSeriesFromProdHartogsSupport_local
    {m : ℕ}
    (ih : ∀ {D' : Set (Fin (m + 1) → ℂ)} {f' : (Fin (m + 1) → ℂ) → ℂ},
      IsOpen D' →
      (∀ z ∈ D', ∀ i : Fin (m + 1), AnalyticAt ℂ (fun w ↦ f' (Function.update z i w)) (z i)) →
      AnalyticOnNhd ℂ f' D')
    {A : ℕ → (Fin (m + 1) → ℂ) → ℂ} {x0 : Fin (m + 1) → ℂ} {u0 : ℂ}
    {r R C : ℝ}
    (hr : 0 < r) (hR : 0 < R)
    (hCoeffOn : ∀ n : ℕ, AnalyticOnNhd ℂ (A n) (Metric.ball x0 r))
    (hCoeffBound : ∀ x ∈ Metric.closedBall x0 (r / 2), ∀ n : ℕ, ‖A n x‖ ≤ C / R ^ n) :
    AnalyticAt ℂ
      (fun p : (Fin (m + 1) → ℂ) × ℂ ↦ ∑' n : ℕ, A n p.1 * (p.2 - u0) ^ n)
      (x0, u0) := by
  have hProdHartogs :
      ∀ {D : Set ((Fin (m + 1) → ℂ) × ℂ)} {G : ((Fin (m + 1) → ℂ) × ℂ) → ℂ},
        IsOpen D →
        (∀ p ∈ D,
          AnalyticAt ℂ (fun w : Fin (m + 1) → ℂ ↦ G (w, p.2)) p.1 ∧
            AnalyticAt ℂ (fun w : ℂ ↦ G (p.1, w)) p.2) →
        AnalyticOnNhd ℂ G D := fun hD hsep ↦
    separatelyHolomorphicProd_analyticOnNhd_local ih hD hsep
  -- Route correction: instantiate the support theorem with the thin local Hartogs callback.
  exact
    analyticAt_parametricPowerSeries_of_uniformCoeffBound_of_prodHartogs_local
      hProdHartogs ih hr hR hCoeffOn hCoeffBound

/-- Helper for Theorem IV.5-extra-2: transporting the local product Hartogs owner back to the
`Fin (m + 2)` model yields joint analyticity on the transported product domain. -/
lemma transportedProductHartogs_ofInduction_local
    {m : ℕ}
    (ih : ∀ {D' : Set (Fin (m + 1) → ℂ)} {f' : (Fin (m + 1) → ℂ) → ℂ},
      IsOpen D' →
      (∀ z ∈ D', ∀ i : Fin (m + 1), AnalyticAt ℂ (fun w ↦ f' (Function.update z i w)) (z i)) →
      AnalyticOnNhd ℂ f' D')
    {D : Set (Fin (m + 2) → ℂ)} {f : (Fin (m + 2) → ℂ) → ℂ}
    (hD : IsOpen D)
    (hsep : ∀ z ∈ D, ∀ i : Fin (m + 2), AnalyticAt ℂ (fun w ↦ f (Function.update z i w)) (z i)) :
    let e := Fin.succFunEquiv ℂ (m + 1)
    let g : (Fin (m + 1) → ℂ) × ℂ → ℂ := f ∘ e.symm
    AnalyticOnNhd ℂ g {p : (Fin (m + 1) → ℂ) × ℂ | e.symm p ∈ D} := by
  dsimp
  have hsymmCont : Continuous (Fin.succFunEquiv ℂ (m + 1)).symm := by
    simpa using continuous_succFunEquiv_symm m
  have hDtransport :
      IsOpen {p : (Fin (m + 1) → ℂ) × ℂ | (Fin.succFunEquiv ℂ (m + 1)).symm p ∈ D} := by
    simpa using hD.preimage hsymmCont
  have hsepTransport :
      ∀ p ∈ {p : (Fin (m + 1) → ℂ) × ℂ | (Fin.succFunEquiv ℂ (m + 1)).symm p ∈ D},
        AnalyticAt ℂ
            (fun x : Fin (m + 1) → ℂ ↦
              (f ∘ (Fin.succFunEquiv ℂ (m + 1)).symm) (x, p.2))
            p.1 ∧
          AnalyticAt ℂ
            (fun w : ℂ ↦
              (f ∘ (Fin.succFunEquiv ℂ (m + 1)).symm) (p.1, w))
            p.2 := by
    simpa [Function.comp] using
      transportedProductSeparateAnalytic_local ih hD hsep
  -- Finish in product coordinates using the local product Hartogs owner.
  simpa [Function.comp] using
    separatelyHolomorphicProd_analyticOnNhd_local ih hDtransport hsepTransport

/-- Helper for Theorem IV.5-extra-2: once the product family is already analytic on the ambient
open set, the compact-torus continuity and the uniform Cauchy coefficient bound follow by simple
restriction to the smaller closed block ball and boundary circle. -/
lemma prodBoundaryCoeffUniformOfAnalyticOnNhd_local
    {m : ℕ}
    {D : Set ((Fin (m + 1) → ℂ) × ℂ)} {G : ((Fin (m + 1) → ℂ) × ℂ) → ℂ}
    (hGOn : AnalyticOnNhd ℂ G D)
    {p : ((Fin (m + 1) → ℂ) × ℂ)} {ρ : ℝ}
    (hρpos : 0 < ρ)
    (hcyl : Metric.ball p.1 (ρ / 2) ×ˢ Metric.closedBall p.2 (ρ / 2) ⊆ D) :
    let w0 : ℂ := p.2
    let r0 : ℝ := ρ / 8
    let r1 : ℝ := r0 / 2
    let A : ℕ → (Fin (m + 1) → ℂ) → ℂ := fun n x ↦
      (cauchyPowerSeries (fun ζ ↦ G (x, ζ)) w0 (ρ / 2)).coeff n
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ x ∈ Metric.closedBall p.1 r1, ∀ n : ℕ, ‖A n x‖ ≤ C / (ρ / 2 : ℝ) ^ n := by
  let w0 : ℂ := p.2
  let r0 : ℝ := ρ / 8
  let r1 : ℝ := r0 / 2
  let A : ℕ → (Fin (m + 1) → ℂ) → ℂ := fun n x ↦
    (cauchyPowerSeries (fun ζ ↦ G (x, ζ)) w0 (ρ / 2)).coeff n
  have hr1_lt_half : r1 < ρ / 2 := by
    -- The closed block ball used by the normalized-series closeout is strictly smaller than the
    -- cylinder radius provided by the product-domain hypothesis.
    dsimp [r1, r0]
    linarith
  have hcont :
      ContinuousOn (Function.uncurry fun x ζ ↦ G (x, ζ))
        (Metric.closedBall p.1 r1 ×ˢ Metric.sphere p.2 (ρ / 2)) := by
    have hsubset :
        Metric.closedBall p.1 r1 ×ˢ Metric.sphere p.2 (ρ / 2) ⊆ D := by
      intro q hq
      refine hcyl ?_
      constructor
      · exact Metric.closedBall_subset_ball hr1_lt_half hq.1
      · exact Metric.sphere_subset_closedBall hq.2
    -- Restrict the ambient analytic owner to the compact torus used by the scalar Cauchy bound.
    simpa [Function.uncurry] using hGOn.continuousOn.mono hsubset
  obtain ⟨C, hCnonneg, hCbound⟩ :=
    cauchyPowerSeries_coeff_uniformBound_of_continuousOn_closedBall
      (by positivity) hcont
  refine ⟨C, hCnonneg, ?_⟩
  intro x hx n
  -- Re-express the generic closed-ball Cauchy package in the local coefficient notation.
  simpa [A, w0] using hCbound x hx n

/-- Helper for Theorem IV.5-extra-2: once joint analyticity is known on the transported product
domain, the boundary Cauchy coefficient package is a direct restriction of the support theorem. -/
lemma transportedBoundaryCoeff_uniformBoundOnClosedSmallBall_local
    {m : ℕ}
    (ih : ∀ {D' : Set (Fin (m + 1) → ℂ)} {f' : (Fin (m + 1) → ℂ) → ℂ},
      IsOpen D' →
      (∀ z ∈ D', ∀ i : Fin (m + 1), AnalyticAt ℂ (fun w ↦ f' (Function.update z i w)) (z i)) →
      AnalyticOnNhd ℂ f' D')
    {D : Set (Fin (m + 2) → ℂ)} {f : (Fin (m + 2) → ℂ) → ℂ}
    (hD : IsOpen D)
    (hsep : ∀ z ∈ D, ∀ i : Fin (m + 2), AnalyticAt ℂ (fun w ↦ f (Function.update z i w)) (z i))
    {z : Fin (m + 2) → ℂ} {ρ : ℝ}
    (hρpos : 0 < ρ)
    (hcyl :
      Metric.ball ((Fin.succFunEquiv ℂ (m + 1) z).1) (ρ / 2) ×ˢ
          Metric.closedBall ((Fin.succFunEquiv ℂ (m + 1) z).2) (ρ / 2) ⊆
        {p | (Fin.succFunEquiv ℂ (m + 1)).symm p ∈ D}) :
    let e := Fin.succFunEquiv ℂ (m + 1)
    let g : (Fin (m + 1) → ℂ) × ℂ → ℂ := f ∘ e.symm
    let w0 : ℂ := (e z).2
    let r0 : ℝ := ρ / 8
    let r1 : ℝ := r0 / 2
    let A : ℕ → (Fin (m + 1) → ℂ) → ℂ := fun n x ↦
      (cauchyPowerSeries (fun ζ ↦ g (x, ζ)) w0 (ρ / 2)).coeff n
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ x ∈ Metric.closedBall (e z).1 r1, ∀ n : ℕ, ‖A n x‖ ≤ C / (ρ / 2 : ℝ) ^ n := by
  dsimp
  have hProdOn :
      AnalyticOnNhd ℂ (f ∘ (Fin.succFunEquiv ℂ (m + 1)).symm)
        {p : (Fin (m + 1) → ℂ) × ℂ | (Fin.succFunEquiv ℂ (m + 1)).symm p ∈ D} := by
    simpa [Function.comp] using
      transportedProductHartogs_ofInduction_local ih hD hsep
  -- Consume the support-level boundary coefficient bound on the transported product domain.
  simpa [Function.comp] using
    prodBoundaryCoeffUniformOfAnalyticOnNhd_local
      hProdOn hρpos hcyl

lemma separatelyHolomorphicAtLeastTwo_analyticOnNhd_ofIH
    {m : ℕ} {D : Set (Fin (m + 2) → ℂ)} {f : (Fin (m + 2) → ℂ) → ℂ}
    (ih : ∀ {D' : Set (Fin (m + 1) → ℂ)} {f' : (Fin (m + 1) → ℂ) → ℂ},
      IsOpen D' →
      (∀ z ∈ D', ∀ i : Fin (m + 1), AnalyticAt ℂ (fun w ↦ f' (Function.update z i w)) (z i)) →
      AnalyticOnNhd ℂ f' D')
    (hD : IsOpen D)
    (hsep : ∀ z ∈ D, ∀ i : Fin (m + 2), AnalyticAt ℂ (fun w ↦ f (Function.update z i w)) (z i)) :
    AnalyticOnNhd ℂ f D := by
  -- Route correction: the target file now only packages the four frontier callbacks expected by
  -- the support-level higher-dimensional Hartogs theorem.
  exact
    separatelyHolomorphicAtLeastTwo_analyticOnNhd_ofIH_fromFrontier_local
      ih hD hsep
      (transportedProductSeparateAnalytic_local ih hD hsep)
      (fun {D2} {F} hD2 hsep2 ↦
        separatelyHolomorphicFin2_analyticOnNhd_independent_local hD2 hsep2)
      (fun {A} {x0} {u0} {r} {R} {C} hr hR hCoeffOn hCoeffBound ↦
        analyticAtParametricPowerSeriesFromProdHartogsSupport_local
          (m := m) ih hr hR hCoeffOn hCoeffBound)
      (fun {z} {ρ} hρpos hcyl ↦
        transportedBoundaryCoeff_uniformBoundOnClosedSmallBall_local
          ih hD hsep hρpos hcyl)

/-- Helper for Theorem IV.5-extra-2: the full theorem follows by induction on the dimension, with
the `Fin 0`, `Fin 1`, and `Fin (m + 2)` cases delegated to the canonical support owners. -/
lemma separatelyHolomorphicAnalyticOnNhdAux (n : ℕ) {D : Set (Fin n → ℂ)} {f : (Fin n → ℂ) → ℂ}
    (hD : IsOpen D)
    (hsep : ∀ z ∈ D, ∀ i : Fin n, AnalyticAt ℂ (fun w ↦ f (Function.update z i w)) (z i)) :
    AnalyticOnNhd ℂ f D := by
  induction n with
  | zero =>
      -- The zero-dimensional source is a singleton.
      exact (separatelyHolomorphicEmpty_analyticOnNhd : AnalyticOnNhd ℂ f D)
  | succ n ih =>
      cases n with
      | zero =>
          -- In one variable the unique coordinate slice is the whole function.
          simpa using separatelyHolomorphicSingleton_analyticOnNhd hsep
      | succ m =>
          -- The higher-dimensional case is exactly the induction-step support theorem.
          simpa using
            separatelyHolomorphicAtLeastTwo_analyticOnNhd_ofIH
              ih hD hsep

/-- Helper for Theorem IV.5-extra-2: the `Fin (m + 2)` statement is the higher-dimensional branch
of the general dimension induction. -/
lemma separatelyHolomorphicAtLeastTwo_analyticOnNhd
    {m : ℕ} {D : Set (Fin (m + 2) → ℂ)} {f : (Fin (m + 2) → ℂ) → ℂ}
    (hD : IsOpen D)
    (hsep : ∀ z ∈ D, ∀ i : Fin (m + 2), AnalyticAt ℂ (fun w ↦ f (Function.update z i w)) (z i)) :
    AnalyticOnNhd ℂ f D := by
  -- Reuse the global induction theorem at the matching dimension.
  simpa using
    separatelyHolomorphicAnalyticOnNhdAux (m + 2) hD hsep

/-- Helper for Theorem IV.5-extra-2: once the continuity-free Hartogs theorem on `Fin (m + 2) → ℂ`
is available, the product-coordinate version on `((Fin (m + 1) → ℂ) × ℂ)` follows immediately by
transport along `Fin.succFunEquiv`. -/
private lemma separatelyHolomorphicProd_analyticOnNhd_from_core_local
    {m : ℕ}
    {D : Set ((Fin (m + 1) → ℂ) × ℂ)} {G : ((Fin (m + 1) → ℂ) × ℂ) → ℂ}
    (hD : IsOpen D)
    (hsep : ∀ p ∈ D,
      AnalyticAt ℂ (fun w : Fin (m + 1) → ℂ ↦ G (w, p.2)) p.1 ∧
        AnalyticAt ℂ (fun w ↦ G (p.1, w)) p.2) :
    AnalyticOnNhd ℂ G D := by
  -- Once the dimension-`m + 2` Hartogs core is proved, the product-domain theorem is only the
  -- standard `Fin.succFunEquiv` transport packaged earlier in this file.
  exact
    productHartogs_ofSuccHartogs_local
      (m := m)
      (hartogsSucc := fun {D' : Set (Fin (m + 2) → ℂ)} {F : (Fin (m + 2) → ℂ) → ℂ} hD' hsep' ↦
        separatelyHolomorphicAnalyticOnNhdAux (m + 2) hD' hsep')
      hD hsep

/-- Helper for Theorem IV.5-extra-2: the continuity-free Hartogs core is exactly the general
dimension induction theorem. -/
private lemma separately_holomorphic_analyticOnNhd_core
    (hD : IsOpen D)
    (hsep : ∀ z ∈ D, ∀ i : Fin n, AnalyticAt ℂ (fun w ↦ f (Function.update z i w)) (z i)) :
    AnalyticOnNhd ℂ f D := by
  -- The support-file induction already proves the continuity-free theorem.
  exact separatelyHolomorphicAnalyticOnNhdAux n hD hsep

/-- Helper for Theorem IV.5-extra-2: on an open set, analyticity immediately yields
differentiability. -/
private lemma separately_holomorphic_differentiableOn
    (hD : IsOpen D)
    (hsep : ∀ z ∈ D, ∀ i : Fin n, AnalyticAt ℂ (fun w ↦ f (Function.update z i w)) (z i)) :
    DifferentiableOn ℂ f D := by
  -- The continuity-free analytic theorem already carries the needed Fréchet differentiability.
  exact
    (separately_holomorphic_analyticOnNhd_core hD hsep).differentiableOn

/-- Helper for Theorem IV.5-extra-2: the source-facing analytic conclusion is just the internal
continuity-free core restated for the public theorem layer. -/
private lemma separately_holomorphic_analyticOnNhd
    (hD : IsOpen D)
    (hsep : ∀ z ∈ D, ∀ i : Fin n, AnalyticAt ℂ (fun w ↦ f (Function.update z i w)) (z i)) :
    AnalyticOnNhd ℂ f D := by
  -- Keep the public theorem layer thin by forwarding directly to the internal core.
  exact separately_holomorphic_analyticOnNhd_core hD hsep

/-- Theorem IV.5-extra-2 (1): if `f` is continuous on an open set `D ⊆ ℂ^n` and for every
`z ∈ D` each coordinate slice `w ↦ f (Function.update z i w)` is holomorphic at `z i`, then `f`
is holomorphic on `D`. -/
theorem continuous_separately_holomorphic_differentiableOn
    (hcont : ContinuousOn f D) (hD : IsOpen D)
    (hsep : ∀ z ∈ D, ∀ i : Fin n, AnalyticAt ℂ (fun w ↦ f (Function.update z i w)) (z i)) :
    DifferentiableOn ℂ f D := by
  let _ := hcont
  -- The proof route is continuity-free; the source-facing continuity hypothesis is retained only
  -- because it belongs to the textbook statement.
  simpa using separately_holomorphic_differentiableOn hD hsep

/-- Theorem IV.5-extra-2 (2): a continuous function on an open set `D ⊆ ℂ^n` whose coordinate
slices are holomorphic at every point of `D` is analytic on `D`. -/
theorem continuous_separately_holomorphic_analyticOnNhd
    (hcont : ContinuousOn f D) (hD : IsOpen D)
    (hsep : ∀ z ∈ D, ∀ i : Fin n, AnalyticAt ℂ (fun w ↦ f (Function.update z i w)) (z i)) :
    AnalyticOnNhd ℂ f D := by
  let _ := hcont
  -- The proof route is continuity-free; the source-facing continuity hypothesis is retained only
  -- because it belongs to the textbook statement.
  simpa using separately_holomorphic_analyticOnNhd hD hsep

/-- Helper for Theorem IV.5-extra-2: for scalar-valued maps on an open subset of `ℂ^n`,
`DifferentiableOn ℂ` and `AnalyticOnNhd ℂ` are equivalent. -/
theorem _root_.DifferentiableOn.analyticOnNhd_pi
    (hf : DifferentiableOn ℂ f D) (hD : IsOpen D) :
    AnalyticOnNhd ℂ f D := by
  have hcont : ContinuousOn f D := hf.continuousOn
  have hsep : ∀ z ∈ D, ∀ i : Fin n, AnalyticAt ℂ (fun w ↦ f (Function.update z i w)) (z i) := by
    intro z hz i
    let s : Set ℂ := {w : ℂ | Function.update z i w ∈ D}
    have hsOpen : IsOpen s := by
      have hupdateCont : Continuous (fun w : ℂ ↦ Function.update z i w) := by
        refine continuous_pi fun j ↦ ?_
        by_cases hj : j = i
        · subst hj
          simpa [Function.update] using (continuous_id : Continuous fun w : ℂ ↦ w)
        · simpa [Function.update, hj] using (continuous_const : Continuous fun _ : ℂ ↦ z j)
      exact hD.preimage hupdateCont
    have hsliceDiff : DifferentiableOn ℂ (fun w ↦ f (Function.update z i w)) s := by
      intro w hw
      have hfAt : DifferentiableAt ℂ f (Function.update z i w) := by
        exact hf.differentiableAt (hD.mem_nhds hw)
      have hupdateAt : DifferentiableAt ℂ (fun u : ℂ ↦ Function.update z i u) w := by
        exact (hasDerivAt_update z i w).differentiableAt
      exact (hfAt.comp w hupdateAt).differentiableWithinAt
    have hzMem : z i ∈ s := by
      simpa [s]
    -- Each coordinate slice is a one-variable holomorphic map on the open preimage cut out by
    -- `Function.update z i`.
    exact (hsliceDiff.analyticOnNhd hsOpen) (z i) hzMem
  -- The public continuity-plus-slices theorem applies directly once the scalar slice holomorphy is
  -- reconstructed from the Fréchet derivative.
  exact continuous_separately_holomorphic_analyticOnNhd hcont hD hsep

end
