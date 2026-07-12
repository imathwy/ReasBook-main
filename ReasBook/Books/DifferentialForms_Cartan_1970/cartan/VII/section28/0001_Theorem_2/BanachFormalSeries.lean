import DifferentialForms_Cartan_1970.VII.section27.«0001_Theorem_I»
import Mathlib

open Filter
open Set

open scoped Topology PowerSeries
open PowerSeries

/-- Helper for Cartan section28 0001_Theorem_2: the scalar coefficient sequence of the identity
map `z ↦ z` packaged as a one-variable formal series. -/
noncomputable def identitySeriesCoeff : ℕ → ℂ
  | 0 => 0
  | 1 => 1
  | _ + 2 => 0

/-- Helper for Cartan section28 0001_Theorem_2: package the formal curve
`z ↦ (z, ∑ aₘ z^m)` with values in `ℂ × E`. -/
noncomputable def oneVariableSeriesOfCoefficients {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℂ E]
    (a : ℕ → E) : FormalMultilinearSeries ℂ ℂ E :=
  fun n ↦ ContinuousMultilinearMap.mkPiRing ℂ (Fin n) (a n)

/-- Helper for Cartan section28 0001_Theorem_2: the coefficient sequence of the packaged
one-variable formal series is exactly the input sequence. -/
theorem oneVariableSeriesOfCoefficients_coeff {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℂ E]
    (a : ℕ → E) (n : ℕ) :
    (oneVariableSeriesOfCoefficients a).coeff n = a n := by
  -- Evaluating the coefficient on the constant-one tuple recovers the stored value.
  simp [oneVariableSeriesOfCoefficients, FormalMultilinearSeries.coeff,
    ContinuousMultilinearMap.mkPiRing_apply]

/-- Helper for Cartan section28 0001_Theorem_2: any summable scalar majorant for the coefficient
sequence gives positive radius to the packaged one-variable series. -/
theorem oneVariableSeriesOfCoefficients_radiusPos_of_summableScalarMajorant
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    {a : ℕ → E} {A : ℕ → ℝ} {r : NNReal}
    (hr : 0 < r) (hsumA : Summable (fun m ↦ A m * (r : ℝ) ^ m))
    (hA : ∀ m, ‖a m‖ ≤ A m) :
    0 < (oneVariableSeriesOfCoefficients a).radius := by
  have howner :
      Summable
        (fun m : ℕ ↦ ‖(oneVariableSeriesOfCoefficients a) m‖ * (r : ℝ) ^ m) := by
    -- Compare the packaged multilinear-term norms directly to the scalar majorant term by term.
    refine Summable.of_nonneg_of_le ?_ ?_ hsumA
    · intro m
      positivity
    · intro m
      calc
        ‖(oneVariableSeriesOfCoefficients a) m‖ * (r : ℝ) ^ m
            = ‖a m‖ * (r : ℝ) ^ m := by
                rw [FormalMultilinearSeries.norm_apply_eq_norm_coef
                  (p := oneVariableSeriesOfCoefficients a) (n := m)]
                rw [oneVariableSeriesOfCoefficients_coeff]
        _ ≤ A m * (r : ℝ) ^ m := by
              exact mul_le_mul_of_nonneg_right (hA m)
                (pow_nonneg (by exact_mod_cast r.2) _)
  have hradius :
      (r : ENNReal) ≤ (oneVariableSeriesOfCoefficients a).radius := by
    exact FormalMultilinearSeries.le_radius_of_summable_norm
      (p := oneVariableSeriesOfCoefficients a) (r := r) howner
  -- Any positive lower bound in `ENNReal` gives the required positive radius.
  exact lt_of_lt_of_le (by simpa [ENNReal.coe_pos] using hr) hradius

/-- Helper for Cartan section28 0001_Theorem_2: package the formal curve
`z ↦ (z, ∑ aₘ z^m)` with values in `ℂ × E`. -/
noncomputable def recenteredCurveSeriesBanach {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℂ E]
    (a : ℕ → E) : FormalMultilinearSeries ℂ ℂ (ℂ × E) :=
  (oneVariableSeriesOfCoefficients identitySeriesCoeff).prod
    (oneVariableSeriesOfCoefficients a)

/-- Helper for Cartan section28 0001_Theorem_2: every Banach-valued one-variable formal series is
recovered from its diagonal coefficient sequence. -/
theorem formalMultilinearSeries_eq_oneVariableSeriesOfCoefficients {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℂ E]
    (P : FormalMultilinearSeries ℂ ℂ E) :
    P = oneVariableSeriesOfCoefficients (fun m ↦ P.coeff m) := by
  -- In one complex variable, the diagonal coefficients determine the whole multilinear owner.
  refine FormalMultilinearSeries.ext fun m ↦ ?_
  rw [← FormalMultilinearSeries.mkPiRing_coeff_eq P m]
  rw [← FormalMultilinearSeries.mkPiRing_coeff_eq
    (oneVariableSeriesOfCoefficients (fun k ↦ P.coeff k)) m]
  congr 1
  exact (oneVariableSeriesOfCoefficients_coeff (a := fun k ↦ P.coeff k) m).symm

/-- Helper for Cartan section28 0001_Theorem_2: pairing the identity coordinate with a centered
Banach-valued one-variable owner produces the canonical recentered curve owner. -/
theorem recenteredCurveSeriesBanach_hasFPowerSeriesAt {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℂ E]
    {u : ℂ → E} {a : ℕ → E}
    (hu : HasFPowerSeriesAt u (oneVariableSeriesOfCoefficients a) 0) :
    HasFPowerSeriesAt (fun z : ℂ ↦ (z, u z)) (recenteredCurveSeriesBanach a) 0 := by
  have hXcoeff :
      ∀ m, ((ContinuousLinearMap.id ℂ ℂ).fpowerSeries 0).coeff m = identitySeriesCoeff m := by
    intro m
    cases m with
    | zero =>
        rw [FormalMultilinearSeries.coeff, ContinuousLinearMap.fpowerSeries_apply_zero,
          ContinuousMultilinearMap.uncurry0_apply, identitySeriesCoeff]
        simp
    | succ m =>
        cases m with
        | zero =>
            rw [FormalMultilinearSeries.coeff, ContinuousLinearMap.fpowerSeries_apply_one,
              continuousMultilinearCurryFin1_symm_apply, identitySeriesCoeff]
            simp
        | succ m =>
            rw [FormalMultilinearSeries.coeff, ContinuousLinearMap.fpowerSeries_apply_add_two,
              identitySeriesCoeff]
            simp
  have hXOwner :
      (ContinuousLinearMap.id ℂ ℂ).fpowerSeries 0 =
        oneVariableSeriesOfCoefficients identitySeriesCoeff := by
    calc
      (ContinuousLinearMap.id ℂ ℂ).fpowerSeries 0
          = oneVariableSeriesOfCoefficients
              (fun m ↦ ((ContinuousLinearMap.id ℂ ℂ).fpowerSeries 0).coeff m) :=
            formalMultilinearSeries_eq_oneVariableSeriesOfCoefficients _
      _ = oneVariableSeriesOfCoefficients identitySeriesCoeff := by
            congr
            funext m
            exact hXcoeff m
  have hX :
      HasFPowerSeriesAt (fun z : ℂ ↦ z)
        (oneVariableSeriesOfCoefficients identitySeriesCoeff)
        0 := by
    -- The identity map already carries the canonical one-variable formal owner.
    simpa [hXOwner, id_eq] using (ContinuousLinearMap.id ℂ ℂ).hasFPowerSeriesAt (0 : ℂ)
  -- Pair the identity owner with the centered Banach-valued owner to obtain the recentered curve.
  simpa [recenteredCurveSeriesBanach] using hX.prod hu

/-- Helper for Cartan section28 0001_Theorem_2: the recentered Banach-valued curve owner combines
the fixed `x`-coefficient and the Banach coefficient by the product norm. -/
theorem recenteredCurveSeriesBanach_norm {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℂ E]
    (a : ℕ → E) (m : ℕ) :
    ‖(recenteredCurveSeriesBanach a) m‖ = max ‖identitySeriesCoeff m‖ ‖a m‖ := by
  -- The product owner splits into the identity component and the Banach-valued coefficient owner.
  change
    ‖((oneVariableSeriesOfCoefficients identitySeriesCoeff) m).prod
        ((oneVariableSeriesOfCoefficients a) m)‖ =
      max ‖identitySeriesCoeff m‖ ‖a m‖
  rw [ContinuousMultilinearMap.opNorm_prod]
  rw [FormalMultilinearSeries.norm_apply_eq_norm_coef
    (p := oneVariableSeriesOfCoefficients identitySeriesCoeff) (n := m)]
  rw [FormalMultilinearSeries.norm_apply_eq_norm_coef
    (p := oneVariableSeriesOfCoefficients a) (n := m)]
  rw [oneVariableSeriesOfCoefficients_coeff, oneVariableSeriesOfCoefficients_coeff]

/-- Helper for Cartan section28 0001_Theorem_2: a weighted coefficient bound on the Banach
sequence propagates to the full recentered curve owner fed into `Q.comp`. -/
theorem recenteredCurveSeriesBanach_weightedCoeffBudget {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℂ E]
    {a : ℕ → E} {ρ D : NNReal}
    (hρD : (ρ : ℝ) ≤ D)
    (ha : ∀ m, ‖a m‖ * (ρ : ℝ) ^ m ≤ D) :
    ∀ m, ‖recenteredCurveSeriesBanach a m‖ * (ρ : ℝ) ^ m ≤ D := by
  intro m
  -- Bound the two product components separately: the fixed identity coefficient and the Banach
  -- coefficient sequence.
  rw [recenteredCurveSeriesBanach_norm]
  rw [max_mul_of_nonneg _ _ (pow_nonneg (by exact_mod_cast ρ.2) _)]
  refine (max_le_iff.2 ?_)
  constructor
  · cases m with
    | zero =>
        simp [identitySeriesCoeff]
    | succ m =>
        cases m with
        | zero =>
            simpa [identitySeriesCoeff] using hρD
        | succ m =>
            simp [identitySeriesCoeff]
  · exact ha m

/-- Helper for Cartan section28 0001_Theorem_2: the degree-`m` coefficient obtained by composing
the Taylor model `Q` with the recentered curve built from `a`. -/
noncomputable def recenteredComposedCoeffBanach {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℂ E]
    (Q : FormalMultilinearSeries ℂ (ℂ × E) E)
    (a : ℕ → E) (m : ℕ) : E :=
  (Q.comp (recenteredCurveSeriesBanach a)).coeff m

/-- Helper for Cartan section28 0001_Theorem_2: the degree-`m` coefficient of a formal composition
depends only on the inner coefficients through degree `m`. -/
theorem comp_coeff_eq_of_coeff_eq_upto_banach {F G : Type*}
    [NormedAddCommGroup F] [NormedSpace ℂ F]
    [NormedAddCommGroup G] [NormedSpace ℂ G]
    {Q : FormalMultilinearSeries ℂ F G} {P P' : FormalMultilinearSeries ℂ ℂ F} {m : ℕ}
    (hPP' : ∀ k ≤ m, P.coeff k = P'.coeff k) :
    (Q.comp P).coeff m = (Q.comp P').coeff m := by
  -- Expand the composition coefficient as the finite sum over compositions of `m`.
  rw [FormalMultilinearSeries.coeff, FormalMultilinearSeries.coeff]
  rw [FormalMultilinearSeries.comp, FormalMultilinearSeries.comp,
    ContinuousMultilinearMap.sum_apply, ContinuousMultilinearMap.sum_apply]
  refine Finset.sum_congr rfl fun c _hc ↦ ?_
  -- Each block in a composition of `m` has size at most `m`, so the relevant inner coefficients
  -- already agree.
  simp only [FormalMultilinearSeries.compAlongComposition_apply]
  refine congrArg (Q c.length) ?_
  funext i
  exact hPP' (c.blocksFun i) (c.blocks_le (c.blocksFun_mem_blocks i))

/-- Helper for Cartan section28 0001_Theorem_2: matching coefficient data through degree `m`
gives the same recentered-curve coefficients through degree `m`. -/
theorem recenteredCurveSeriesBanach_coeff_eq_of_prefix {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℂ E]
    {a b : ℕ → E} {m : ℕ}
    (hab : ∀ k ≤ m, a k = b k) :
    ∀ k ≤ m,
      (recenteredCurveSeriesBanach a).coeff k = (recenteredCurveSeriesBanach b).coeff k := by
  intro k hk
  refine Prod.ext rfl ?_
  calc
    ((recenteredCurveSeriesBanach a).coeff k).2 = (oneVariableSeriesOfCoefficients a).coeff k := rfl
    _ = a k := by rw [oneVariableSeriesOfCoefficients_coeff]
    _ = b k := hab k hk
    _ = (oneVariableSeriesOfCoefficients b).coeff k := by
          rw [oneVariableSeriesOfCoefficients_coeff]
    _ = ((recenteredCurveSeriesBanach b).coeff k).2 := rfl

/-- Helper for Cartan section28 0001_Theorem_2: the recentered composition coefficient is
triangular in the prefix data of the coefficient sequence. -/
theorem recenteredComposedCoeff_eq_of_prefix_banach {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℂ E]
    (Q : FormalMultilinearSeries ℂ (ℂ × E) E)
    {a b : ℕ → E} {m : ℕ}
    (hab : ∀ k ≤ m, a k = b k) :
    recenteredComposedCoeffBanach Q a m = recenteredComposedCoeffBanach Q b m := by
  -- The generic composition lemma applies once the recentered-curve coefficients match.
  exact comp_coeff_eq_of_coeff_eq_upto_banach
    (Q := Q) (P := recenteredCurveSeriesBanach a) (P' := recenteredCurveSeriesBanach b)
    (recenteredCurveSeriesBanach_coeff_eq_of_prefix hab)

/-- Helper for Cartan section28 0001_Theorem_2: the stage-`m` approximant stores the first `m`
coefficients forced by the exact recentered Banach-valued recursion. -/
noncomputable def formalSeriesSolutionApproximantCoeff {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℂ E]
    (Q : FormalMultilinearSeries ℂ (ℂ × E) E) : ℕ → ℕ → E
  | 0, _ => 0
  | m + 1, k =>
      if k ≤ m then
        formalSeriesSolutionApproximantCoeff Q m k
      else if k = m + 1 then
        ((m + 1 : ℂ)⁻¹) • recenteredComposedCoeffBanach Q
          (formalSeriesSolutionApproximantCoeff Q m) m
      else
        0

/-- Helper for Cartan section28 0001_Theorem_2: once a coefficient has appeared, later stages do
not change it. -/
theorem formalSeriesSolutionApproximantCoeff_step_eq {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℂ E]
    (Q : FormalMultilinearSeries ℂ (ℂ × E) E) {m k : ℕ} (hkm : k ≤ m) :
    formalSeriesSolutionApproximantCoeff Q (m + 1) k =
      formalSeriesSolutionApproximantCoeff Q m k := by
  -- The recursive step only changes the new coefficient in degree `m + 1`.
  simp [formalSeriesSolutionApproximantCoeff, hkm]

/-- Helper for Cartan section28 0001_Theorem_2: stage `m + 1` inserts exactly the coefficient
required by the recentered Banach-valued recursion. -/
theorem formalSeriesSolutionApproximantCoeff_next_eq {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℂ E]
    (Q : FormalMultilinearSeries ℂ (ℂ × E) E) (m : ℕ) :
    formalSeriesSolutionApproximantCoeff Q (m + 1) (m + 1) =
      ((m + 1 : ℂ)⁻¹) • recenteredComposedCoeffBanach Q
        (formalSeriesSolutionApproximantCoeff Q m) m := by
  -- At degree `m + 1` the new stage hits the defining recursion branch.
  simp [formalSeriesSolutionApproximantCoeff]

/-- Helper for Cartan section28 0001_Theorem_2: once a coefficient is created, all later
approximants keep that value. -/
theorem formalSeriesSolutionApproximantCoeff_stabilizes {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℂ E]
    (Q : FormalMultilinearSeries ℂ (ℂ × E) E) (m k : ℕ) :
    formalSeriesSolutionApproximantCoeff Q (m + k) m =
      formalSeriesSolutionApproximantCoeff Q m m := by
  induction k with
  | zero =>
      simp
  | succ k ih =>
      -- The `m`th coefficient is already present at stage `m + k`, so the next stage keeps it.
      have hstep :
          formalSeriesSolutionApproximantCoeff Q (m + k + 1) m =
            formalSeriesSolutionApproximantCoeff Q (m + k) m := by
        simpa [Nat.add_assoc] using
          formalSeriesSolutionApproximantCoeff_step_eq
            (Q := Q) (m := m + k) (k := m) (Nat.le_add_right m k)
      calc
        formalSeriesSolutionApproximantCoeff Q (m + (k + 1)) m
            = formalSeriesSolutionApproximantCoeff Q (m + k + 1) m := by
                simp [Nat.add_assoc]
        _ = formalSeriesSolutionApproximantCoeff Q (m + k) m := hstep
        _ = formalSeriesSolutionApproximantCoeff Q m m := ih

/-- Helper for Cartan section28 0001_Theorem_2: the stabilized coefficients define the exact
one-variable formal series solving the Banach-valued recursion. -/
noncomputable def formalSeriesSolutionSeries {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℂ E]
    (Q : FormalMultilinearSeries ℂ (ℂ × E) E) :
    FormalMultilinearSeries ℂ ℂ E :=
  oneVariableSeriesOfCoefficients fun m ↦
    formalSeriesSolutionApproximantCoeff Q m m

/-- Helper for Cartan section28 0001_Theorem_2: the stabilized formal series agrees with every
later approximant through the available coefficient prefix. -/
theorem formalSeriesSolutionSeries_coeff_eq_approximant {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℂ E]
    (Q : FormalMultilinearSeries ℂ (ℂ × E) E) {m k : ℕ} (hmk : m ≤ k) :
    (formalSeriesSolutionSeries Q).coeff m =
      formalSeriesSolutionApproximantCoeff Q k m := by
  -- Read the coefficient from its defining stage and then use stabilization.
  calc
    (formalSeriesSolutionSeries Q).coeff m
        = formalSeriesSolutionApproximantCoeff Q m m := by
            rw [formalSeriesSolutionSeries, oneVariableSeriesOfCoefficients_coeff]
    _ = formalSeriesSolutionApproximantCoeff Q (m + (k - m)) m := by
          symm
          exact formalSeriesSolutionApproximantCoeff_stabilizes (Q := Q) m (k - m)
    _ = formalSeriesSolutionApproximantCoeff Q k m := by
          rw [Nat.add_sub_of_le hmk]

/-- Helper for Cartan section28 0001_Theorem_2: the stabilized Banach-valued formal series has
vanishing constant coefficient. -/
theorem formalSeriesSolutionSeries_coeff_zero {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℂ E]
    (Q : FormalMultilinearSeries ℂ (ℂ × E) E) :
    (formalSeriesSolutionSeries Q).coeff 0 = 0 := by
  -- Stage `0` is the zero approximant, so the constant coefficient stays zero.
  rw [formalSeriesSolutionSeries, oneVariableSeriesOfCoefficients_coeff]
  simp [formalSeriesSolutionApproximantCoeff]

/-- Helper for Cartan section28 0001_Theorem_2: the stabilized Banach-valued formal series
satisfies the exact recentered coefficient recursion. -/
theorem formalSeriesSolutionSeries_next_coeff_eq {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℂ E]
    (Q : FormalMultilinearSeries ℂ (ℂ × E) E) (m : ℕ) :
    (formalSeriesSolutionSeries Q).coeff (m + 1) =
      ((m + 1 : ℂ)⁻¹) • recenteredComposedCoeffBanach Q
        (fun k ↦ (formalSeriesSolutionSeries Q).coeff k) m := by
  -- Compare the stage-`m` prefix with the stabilized series, then rewrite the new coefficient.
  have hprefix :
      ∀ k ≤ m,
        formalSeriesSolutionApproximantCoeff Q m k =
          (formalSeriesSolutionSeries Q).coeff k := by
    intro k hk
    symm
    exact formalSeriesSolutionSeries_coeff_eq_approximant (Q := Q) hk
  calc
    (formalSeriesSolutionSeries Q).coeff (m + 1)
        = formalSeriesSolutionApproximantCoeff Q (m + 1) (m + 1) := by
            rw [formalSeriesSolutionSeries, oneVariableSeriesOfCoefficients_coeff]
    _ = ((m + 1 : ℂ)⁻¹) • recenteredComposedCoeffBanach Q
          (formalSeriesSolutionApproximantCoeff Q m) m := by
            exact formalSeriesSolutionApproximantCoeff_next_eq (Q := Q) m
    _ = ((m + 1 : ℂ)⁻¹) • recenteredComposedCoeffBanach Q
          (fun k ↦ (formalSeriesSolutionSeries Q).coeff k) m := by
            have hcomp :
                recenteredComposedCoeffBanach Q
                    (formalSeriesSolutionApproximantCoeff Q m) m =
                  recenteredComposedCoeffBanach Q
                    (fun k ↦ (formalSeriesSolutionSeries Q).coeff k) m :=
              recenteredComposedCoeff_eq_of_prefix_banach (Q := Q) hprefix
            simpa using congrArg (fun v : E ↦ ((m + 1 : ℂ)⁻¹) • v) hcomp

/-- Helper for Cartan section28 0001_Theorem_2: the exact recentered Banach-valued coefficient
recursion has a unique one-variable formal solution. -/
theorem existsUnique_formalSeries_solution_for_recentered_banach_system {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℂ E]
    (Q : FormalMultilinearSeries ℂ (ℂ × E) E) :
    ∃! P : FormalMultilinearSeries ℂ ℂ E,
      P.coeff 0 = 0 ∧
      ∀ m, P.coeff (m + 1) =
        ((m + 1 : ℂ)⁻¹) • recenteredComposedCoeffBanach Q (fun k ↦ P.coeff k) m := by
  -- Route correction: solve the formal coefficient recursion first, before the majorant and
  -- convergence steps that will later realize the series analytically.
  let P : FormalMultilinearSeries ℂ ℂ E := formalSeriesSolutionSeries Q
  have hP0 : P.coeff 0 = 0 := formalSeriesSolutionSeries_coeff_zero (Q := Q)
  have hPrec :
      ∀ m, P.coeff (m + 1) =
        ((m + 1 : ℂ)⁻¹) • recenteredComposedCoeffBanach Q (fun k ↦ P.coeff k) m := by
    intro m
    exact formalSeriesSolutionSeries_next_coeff_eq (Q := Q) m
  refine ⟨P, ⟨hP0, hPrec⟩, ?_⟩
  intro Ψ hΨ
  rcases hΨ with ⟨hΨ0, hΨrec⟩
  have hcoeff :
      ∀ d, ∀ k ≤ d, P.coeff k = Ψ.coeff k := by
    intro d
    induction d with
    | zero =>
        intro k hk
        have hk0 : k = 0 := Nat.eq_zero_of_le_zero hk
        subst hk0
        simp [hP0, hΨ0]
    | succ d ih =>
        intro k hk
        by_cases hkd : k ≤ d
        · exact ih k hkd
        · have hk_eq : k = d + 1 := by
            omega
          subst hk_eq
          have hcomp :
              recenteredComposedCoeffBanach Q (fun m ↦ P.coeff m) d =
                recenteredComposedCoeffBanach Q (fun m ↦ Ψ.coeff m) d :=
            recenteredComposedCoeff_eq_of_prefix_banach (Q := Q) (fun m hm ↦ ih m hm)
          simpa [hPrec d, hΨrec d] using
            congrArg (fun v : E ↦ ((d + 1 : ℂ)⁻¹) • v) hcomp
  funext n
  rw [← FormalMultilinearSeries.mkPiRing_coeff_eq P n,
    ← FormalMultilinearSeries.mkPiRing_coeff_eq Ψ n]
  exact (ContinuousMultilinearMap.mkPiRing_eq_iff (R := ℂ) (ι := Fin n) (M := E)).mpr
    (hcoeff n n le_rfl).symm

/-- Helper for Cartan section28 0001_Theorem_2: once a Banach-valued parameter coefficient system
is available, the exact recentered formal recursion has a unique one-variable solution in that
Banach carrier. -/
theorem existsParameterFormalSolutionOfCoefficientSystem {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℂ E]
    (QB : FormalMultilinearSeries ℂ (ℂ × E) E) :
    ∃! P : FormalMultilinearSeries ℂ ℂ E,
      P.coeff 0 = 0 ∧
      ∀ m, P.coeff (m + 1) =
        ((m + 1 : ℂ)⁻¹) • recenteredComposedCoeffBanach QB (fun k ↦ P.coeff k) m :=
  existsUnique_formalSeries_solution_for_recentered_banach_system QB

/-- Helper for Cartan section28 0001_Theorem_2: package the Banach coefficient norms of a
one-variable formal solution as a scalar majorant series. -/
noncomputable def scalarNormSeriesBanach {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℂ E]
    (a : ℕ → E) : ℝ⟦X⟧ :=
  PowerSeries.mk fun m ↦ ‖a m‖

/-- Helper for Cartan section28 0001_Theorem_2: package the operator norms of a Banach-valued
outer owner as a scalar power series. -/
noncomputable def formalMultilinearSeriesNormSeriesBanach {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℂ E]
    (Q : FormalMultilinearSeries ℂ (ℂ × E) E) : ℝ⟦X⟧ :=
  PowerSeries.mk fun m ↦ ‖Q m‖

/-- Helper for Cartan section28 0001_Theorem_2: every coefficient of the scalar majorant
`X + ∑ ‖aₘ‖ X^m` is nonnegative. -/
theorem scalarMajorantSeriesCoeff_nonnegBanach {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℂ E]
    (a : ℕ → E) (m : ℕ) :
    0 ≤ PowerSeries.coeff m ((X : ℝ⟦X⟧) + scalarNormSeriesBanach a) := by
  cases m with
  | zero =>
      -- The constant coefficient vanishes because both summands start at `0`.
      simp [scalarNormSeriesBanach]
  | succ m =>
      cases m with
      | zero =>
          -- In degree `1`, the majorant records the `X` term and the first Banach coefficient.
          have h : 0 ≤ (1 : ℝ) + ‖a 1‖ := by positivity
          simpa [PowerSeries.coeff_X, scalarNormSeriesBanach] using h
      | succ m =>
          -- Higher coefficients are exactly Banach norms.
          simp [PowerSeries.coeff_X, scalarNormSeriesBanach]

/-- Helper for Cartan section28 0001_Theorem_2: the Banach recentered curve coefficient is
dominated by the corresponding coefficient of the scalar majorant `X + ∑ ‖aₘ‖ X^m`. -/
theorem recenteredCurveSeriesBanach_norm_le_scalarMajorantCoeff {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℂ E]
    {a : ℕ → E} (ha0 : a 0 = 0) (m : ℕ) :
    ‖recenteredCurveSeriesBanach a m‖ ≤
      PowerSeries.coeff m ((X : ℝ⟦X⟧) + scalarNormSeriesBanach a) := by
  cases m with
  | zero =>
      -- The degree-`0` recentered coefficient vanishes because both components do.
      rw [recenteredCurveSeriesBanach_norm]
      simp [identitySeriesCoeff, scalarNormSeriesBanach, ha0]
  | succ m =>
      cases m with
      | zero =>
          -- In degree `1`, the majorant contains both the identity coefficient and the first
          -- Banach coefficient.
          rw [recenteredCurveSeriesBanach_norm]
          refine (max_le_iff.2 ?_)
          constructor
          · simp [identitySeriesCoeff, scalarNormSeriesBanach]
          · simp [scalarNormSeriesBanach]
      | succ m =>
          -- In higher degrees only the Banach coefficient survives on the recentered curve side.
          rw [recenteredCurveSeriesBanach_norm]
          have h :
              max ‖identitySeriesCoeff (m + 2)‖ ‖a (m + 2)‖ ≤ ‖a (m + 2)‖ := by
            simp [identitySeriesCoeff]
          exact le_trans h <| by
            simp [PowerSeries.coeff_X, scalarNormSeriesBanach]

/-- Helper for Cartan section28 0001_Theorem_2: the norm of each Banach recentered composition
coefficient is controlled by the corresponding scalar substitution coefficient. -/
theorem recenteredComposedCoeffBanach_norm_le_scalarSubstCoeff {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℂ E]
    (Q : FormalMultilinearSeries ℂ (ℂ × E) E)
    {a : ℕ → E} (ha0 : a 0 = 0) (m : ℕ) :
    ‖recenteredComposedCoeffBanach Q a m‖ ≤
      PowerSeries.coeff m
        ((formalMultilinearSeriesNormSeriesBanach Q).subst
          ((X : ℝ⟦X⟧) + scalarNormSeriesBanach a)) := by
  let U : ℝ⟦X⟧ := (X : ℝ⟦X⟧) + scalarNormSeriesBanach a
  have hU0 : PowerSeries.constantCoeff U = 0 := by
    -- The scalar majorant starts with constant coefficient `0`.
    simp [U, scalarNormSeriesBanach, ha0]
  calc
    ‖recenteredComposedCoeffBanach Q a m‖
        = ‖∑ c : Composition m,
            Q c.length (fun i ↦ (recenteredCurveSeriesBanach a).coeff (c.blocksFun i))‖ := by
              -- Expand the composed coefficient into the standard finite sum over compositions.
              rw [recenteredComposedCoeffBanach, FormalMultilinearSeries.coeff,
                FormalMultilinearSeries.comp, ContinuousMultilinearMap.sum_apply]
              refine congrArg norm ?_
              refine Finset.sum_congr rfl ?_
              intro c hc
              simp only [FormalMultilinearSeries.compAlongComposition_apply]
              refine congrArg (Q c.length) ?_
              funext i
              simp [FormalMultilinearSeries.applyComposition]
    _ ≤ ∑ c : Composition m,
          ‖Q c.length (fun i ↦ (recenteredCurveSeriesBanach a).coeff (c.blocksFun i))‖ := by
            -- Take norms termwise in the finite composition sum.
            exact norm_sum_le _ _
    _ ≤ ∑ c : Composition m,
          ‖Q c.length‖ * ∏ i : Fin c.length, PowerSeries.coeff (c.blocksFun i) U := by
            -- Bound each multilinear term by the operator norm of `Q` and the scalar majorant of
            -- the recentered curve coefficients.
            refine Finset.sum_le_sum ?_
            intro c hc
            calc
              ‖Q c.length (fun i ↦ (recenteredCurveSeriesBanach a).coeff (c.blocksFun i))‖
                  ≤ ‖Q c.length‖ * ∏ i : Fin c.length,
                      ‖(recenteredCurveSeriesBanach a).coeff (c.blocksFun i)‖ := by
                        exact ContinuousMultilinearMap.le_opNorm (Q c.length) _
              _ ≤ ‖Q c.length‖ * ∏ i : Fin c.length,
                    PowerSeries.coeff (c.blocksFun i) U := by
                      gcongr with i
                      simpa [FormalMultilinearSeries.norm_apply_eq_norm_coef, U] using
                        recenteredCurveSeriesBanach_norm_le_scalarMajorantCoeff
                          (a := a) ha0 (c.blocksFun i)
    _ =
        ((FormalMultilinearSeries.ofScalars ℝ
            (fun k ↦ ‖Q k‖)).comp
          (FormalMultilinearSeries.ofScalars ℝ (fun k ↦ PowerSeries.coeff k U))).coeff m := by
            -- Repackage the finite composition sum as the coefficient of the scalar composed owner.
            symm
            simpa [formalMultilinearSeriesNormSeriesBanach] using
              ofScalars_comp_coeff_eq_sum_compositions
                (formalMultilinearSeriesNormSeriesBanach Q) U m
    _ = PowerSeries.coeff m ((formalMultilinearSeriesNormSeriesBanach Q).subst U) := by
          -- Then identify that composed scalar owner with the scalar substitution series.
          simpa [formalMultilinearSeriesNormSeriesBanach] using
            (scalar_subst_coeff_eq_ofScalars_comp_coeff
              (formalMultilinearSeriesNormSeriesBanach Q) U hU0 m).symm

/-- Helper for Cartan section28 0001_Theorem_2: the exact Banach formal solution is coefficientwise
majorized by the scalar fixed point of the norm owner. -/
theorem formalSeriesSolutionSeries_norm_le_scalarFixedPoint {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℂ E]
    (Q : FormalMultilinearSeries ℂ (ℂ × E) E)
    {Φ : ℝ⟦X⟧} (hΦ0 : PowerSeries.constantCoeff Φ = 0)
    (hΦrec : ∀ m, PowerSeries.coeff (m + 1) Φ =
      ((m + 1 : ℝ)⁻¹) * PowerSeries.coeff m
        ((formalMultilinearSeriesNormSeriesBanach Q).subst ((X : ℝ⟦X⟧) + Φ)))
    (hΦnonneg : ∀ m, 0 ≤ PowerSeries.coeff m Φ) :
    ∀ m, ‖(formalSeriesSolutionSeries Q).coeff m‖ ≤ PowerSeries.coeff m Φ := by
  have hξ0 : (formalSeriesSolutionSeries Q).coeff 0 = 0 :=
    formalSeriesSolutionSeries_coeff_zero (Q := Q)
  have hξrec :
      ∀ m, (formalSeriesSolutionSeries Q).coeff (m + 1) =
        ((m + 1 : ℂ)⁻¹) •
          recenteredComposedCoeffBanach Q
            (fun k ↦ (formalSeriesSolutionSeries Q).coeff k) m := by
    intro m
    exact formalSeriesSolutionSeries_next_coeff_eq (Q := Q) m
  have hSnonneg :
      ∀ d, 0 ≤ PowerSeries.coeff d (formalMultilinearSeriesNormSeriesBanach Q) := by
    intro d
    -- The scalar norm owner has nonnegative coefficients because they are operator norms.
    simp [formalMultilinearSeriesNormSeriesBanach]
  have hξnorm :
      ∀ M, ∀ k ≤ M, ‖(formalSeriesSolutionSeries Q).coeff k‖ ≤ PowerSeries.coeff k Φ := by
    intro M
    induction M with
    | zero =>
        intro k hk
        have hk0 : k = 0 := Nat.eq_zero_of_le_zero hk
        subst hk0
        -- Both the Banach formal solution and the scalar fixed point start at `0`.
        simp [PowerSeries.coeff_zero_eq_constantCoeff_apply, hξ0, hΦ0]
    | succ M ih =>
        intro k hk
        by_cases hkM : k ≤ M
        · exact ih k hkM
        · have hk_eq : k = M + 1 := by omega
          subst hk_eq
          have ha0 : (fun k ↦ (formalSeriesSolutionSeries Q).coeff k) 0 = 0 := by
            simpa using hξ0
          let U : ℝ⟦X⟧ :=
            (X : ℝ⟦X⟧) +
              scalarNormSeriesBanach (fun k ↦ (formalSeriesSolutionSeries Q).coeff k)
          let V : ℝ⟦X⟧ := (X : ℝ⟦X⟧) + Φ
          have hU0 : PowerSeries.constantCoeff U = 0 := by
            -- The Banach majorant series also starts at `0`.
            simp [U, scalarNormSeriesBanach, ha0]
          have hV0 : PowerSeries.constantCoeff V = 0 := by
            simp [V, hΦ0]
          have hU_nonneg : ∀ j ≤ M, 0 ≤ PowerSeries.coeff j U := by
            intro j hj
            -- Every coefficient of the Banach majorant is nonnegative.
            simpa [U] using
              scalarMajorantSeriesCoeff_nonnegBanach
                (a := fun k ↦ (formalSeriesSolutionSeries Q).coeff k) j
          have hV_nonneg : ∀ j ≤ M, 0 ≤ PowerSeries.coeff j V := by
            intro j hj
            -- Adding `X` preserves coefficientwise nonnegativity of the scalar fixed point.
            cases j with
            | zero =>
                simp [V, hΦ0]
            | succ j =>
                cases j with
                | zero =>
                    have hΦ1 : 0 ≤ PowerSeries.coeff 1 Φ := hΦnonneg 1
                    simpa [V] using add_nonneg (show (0 : ℝ) ≤ 1 by norm_num) hΦ1
                | succ j =>
                    simpa [V, PowerSeries.coeff_X] using hΦnonneg (j + 2)
          have hU_le_V : ∀ j ≤ M, PowerSeries.coeff j U ≤ PowerSeries.coeff j V := by
            intro j hj
            cases j with
            | zero =>
                simp [U, V, scalarNormSeriesBanach, ha0, hΦ0]
            | succ j =>
                cases j with
                | zero =>
                    have hstep :
                        ‖(formalSeriesSolutionSeries Q).coeff 1‖ ≤ PowerSeries.coeff 1 Φ :=
                      ih 1 hj
                    simpa [U, V, scalarNormSeriesBanach] using add_le_add_left hstep 1
                | succ j =>
                    have hj' : j + 2 ≤ M := by omega
                    simpa [U, V, scalarNormSeriesBanach, PowerSeries.coeff_X] using
                      ih (j + 2) hj'
          have hsubst_le :
              PowerSeries.coeff M ((formalMultilinearSeriesNormSeriesBanach Q).subst U) ≤
                PowerSeries.coeff M ((formalMultilinearSeriesNormSeriesBanach Q).subst V) := by
            -- The scalar substitution monotonicity is the only bridge between the Banach recursion
            -- and the scalar fixed point recursion.
            exact coeffSubst_mono_of_nonnegative_prefixMajorant hSnonneg hU0 hV0
              hU_nonneg hV_nonneg hU_le_V
          have hnormRec :
              ‖(formalSeriesSolutionSeries Q).coeff (M + 1)‖ =
                ((M + 1 : ℝ)⁻¹) *
                  ‖recenteredComposedCoeffBanach Q
                    (fun k ↦ (formalSeriesSolutionSeries Q).coeff k) M‖ := by
            have hInvNorm : ‖((M + 1 : ℂ)⁻¹)‖ = ((M + 1 : ℝ)⁻¹) := by
              have hNatNormAbs : ‖(M + 1 : ℂ)‖ = |(M + 1 : ℝ)| := by
                simpa using (Complex.norm_real (M + 1 : ℝ))
              have hNatNonneg : 0 ≤ (M + 1 : ℝ) := by positivity
              rw [norm_inv]
              congr 1
              rw [hNatNormAbs, abs_of_nonneg hNatNonneg]
            -- Rewrite the Banach recursion and compute the norm of the scalar factor.
            calc
              ‖(formalSeriesSolutionSeries Q).coeff (M + 1)‖
                  =
                    ‖((M + 1 : ℂ)⁻¹) •
                      recenteredComposedCoeffBanach Q
                        (fun k ↦ (formalSeriesSolutionSeries Q).coeff k) M‖ := by
                          rw [hξrec M]
              _ = ‖((M + 1 : ℂ)⁻¹)‖ *
                    ‖recenteredComposedCoeffBanach Q
                      (fun k ↦ (formalSeriesSolutionSeries Q).coeff k) M‖ := by
                        rw [norm_smul]
              _ = ((M + 1 : ℝ)⁻¹) *
                    ‖recenteredComposedCoeffBanach Q
                      (fun k ↦ (formalSeriesSolutionSeries Q).coeff k) M‖ := by
                        rw [hInvNorm]
          -- Compare the Banach recursion coefficient with the scalar fixed point recursion.
          calc
            ‖(formalSeriesSolutionSeries Q).coeff (M + 1)‖
                = ((M + 1 : ℝ)⁻¹) *
                    ‖recenteredComposedCoeffBanach Q
                      (fun k ↦ (formalSeriesSolutionSeries Q).coeff k) M‖ := hnormRec
            _ ≤ ((M + 1 : ℝ)⁻¹) * PowerSeries.coeff M
                  ((formalMultilinearSeriesNormSeriesBanach Q).subst U) := by
                    gcongr
                    exact recenteredComposedCoeffBanach_norm_le_scalarSubstCoeff
                      (Q := Q) ha0 M
            _ ≤ ((M + 1 : ℝ)⁻¹) * PowerSeries.coeff M
                  ((formalMultilinearSeriesNormSeriesBanach Q).subst V) := by
                    exact mul_le_mul_of_nonneg_left hsubst_le (by positivity)
            _ = PowerSeries.coeff (M + 1) Φ := by
                  simpa [V] using (hΦrec M).symm
  exact fun m ↦ hξnorm m m le_rfl

/-- Helper for Cartan section28 0001_Theorem_2: a Banach-valued recentered owner with positive
radius yields a convergent exact formal solution series. -/
theorem formalSeriesSolutionSeries_radiusPos_of_positiveOwnerRadius {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℂ E]
    {Q : FormalMultilinearSeries ℂ (ℂ × E) E}
    (hQrad : 0 < Q.radius) :
    0 < (formalSeriesSolutionSeries Q).radius := by
  let S : ℝ⟦X⟧ := formalMultilinearSeriesNormSeriesBanach Q
  have hSrad : 0 < S.radius := by
    -- The scalar norm owner inherits positive radius from the Banach multilinear owner.
    rcases ENNReal.lt_iff_exists_nnreal_btwn.mp hQrad with ⟨r, hrpos, hrQ⟩
    have hradius :
        (r : ENNReal) ≤ S.radius := by
      change
        (r : ENNReal) ≤
          (FormalMultilinearSeries.ofScalars ℝ
            (fun m ↦ PowerSeries.coeff m (formalMultilinearSeriesNormSeriesBanach Q))).radius
      apply FormalMultilinearSeries.le_radius_of_summable_norm
      simpa [S, formalMultilinearSeriesNormSeriesBanach, FormalMultilinearSeries.ofScalars_norm]
        using Q.summable_norm_mul_pow hrQ
    exact lt_of_lt_of_le (by simpa [ENNReal.coe_pos] using hrpos) hradius
  obtain ⟨Φ, hΦ0, hΦrec⟩ := existsScalarSubstFormalSolution S
  have hS0 : 0 ≤ PowerSeries.constantCoeff S := by
    -- The constant coefficient of the norm owner is a norm.
    simp [S, formalMultilinearSeriesNormSeriesBanach]
  have hSnonneg : ∀ d, 0 ≤ PowerSeries.coeff d S := by
    intro d
    -- Every coefficient of the norm owner is nonnegative.
    simp [S, formalMultilinearSeriesNormSeriesBanach]
  have hΦnonneg : ∀ m, 0 ≤ PowerSeries.coeff m Φ :=
    scalarSubstFormalSolution_coeff_nonneg hSnonneg hΦ0 hΦrec
  have hΦrad : 0 < Φ.radius :=
    scalarSubstFormalSolution_radiusPos hS0 hSrad hΦ0 hΦrec
  have hmajorant :
      ∀ m, ‖(formalSeriesSolutionSeries Q).coeff m‖ ≤ PowerSeries.coeff m Φ :=
    formalSeriesSolutionSeries_norm_le_scalarFixedPoint
      (Q := Q) hΦ0 hΦrec hΦnonneg
  rcases ENNReal.lt_iff_exists_nnreal_btwn.mp hΦrad with ⟨r, hr0, hrΦ⟩
  have hr0' : 0 < r := by
    simpa [NNReal.coe_pos] using hr0
  have hsumΦ :
      Summable (fun m : ℕ ↦ PowerSeries.coeff m Φ * (r : ℝ) ^ m) := by
    -- Inside the scalar fixed-point radius, the weighted coefficients are summable.
    simpa [Real.norm_eq_abs, abs_of_nonneg, hΦnonneg] using
      (summable_norm_coeff_mul_pow_of_lt_radius Φ hrΦ)
  -- Feed the scalar majorant into the packaged one-variable radius criterion.
  have hradius :
      0 < (oneVariableSeriesOfCoefficients
        (fun m ↦ formalSeriesSolutionApproximantCoeff Q m m)).radius := by
    refine oneVariableSeriesOfCoefficients_radiusPos_of_summableScalarMajorant
      (a := fun m ↦ formalSeriesSolutionApproximantCoeff Q m m)
      (A := fun m ↦ PowerSeries.coeff m Φ) hr0' hsumΦ ?_
    intro m
    have hcoeff :
        (formalSeriesSolutionSeries Q).coeff m = formalSeriesSolutionApproximantCoeff Q m m := by
      simpa using
        (formalSeriesSolutionSeries_coeff_eq_approximant (Q := Q) (m := m) (k := m) le_rfl)
    simpa [hcoeff] using hmajorant m
  simpa [formalSeriesSolutionSeries] using hradius

/-- Helper for Cartan section28 0001_Theorem_2: once the Banach formal solution series has
positive radius, choose a concrete smaller `x`-ball on which it is analytically realized. -/
theorem banachFormalSolutionOnShrunkBall {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
    {Q : FormalMultilinearSeries ℂ (ℂ × E) E}
    (hQrad : 0 < Q.radius) :
    ∃ Rx : ℝ, 0 < Rx ∧
      HasFPowerSeriesOnBall
        (formalSeriesSolutionSeries Q).sum
        (formalSeriesSolutionSeries Q)
        0
        (ENNReal.ofReal Rx) := by
  have hPrad :
      0 < (formalSeriesSolutionSeries Q).radius :=
    formalSeriesSolutionSeries_radiusPos_of_positiveOwnerRadius (Q := Q) hQrad
  rcases ENNReal.lt_iff_exists_nnreal_btwn.mp hPrad with ⟨r, hr0, hrlt⟩
  refine ⟨r, ?_, ?_⟩
  · simpa [NNReal.coe_pos] using hr0
  · -- Realize the formal series on its full radius and then restrict to the chosen smaller ball.
    exact
      ((formalSeriesSolutionSeries Q).hasFPowerSeriesOnBall hPrad).mono
        (by simpa [ENNReal.ofReal_eq_coe_nnreal] using hr0)
        (by simpa [ENNReal.ofReal_eq_coe_nnreal] using hrlt.le)
