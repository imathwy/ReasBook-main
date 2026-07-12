import Mathlib

open scoped Topology BigOperators MvPowerSeries PowerSeries
open PowerSeries

/-- Helper for Theorem I: the recentered curve uses the scalar coefficient sequence of `X`. -/
noncomputable def recenteredXCoeff : ℕ → ℂ
  | 0 => 0
  | 1 => 1
  | _ + 2 => 0

/-- Helper for Theorem I: package the formal curve `z ↦ (z, ∑ aₖ z^k)` as a one-variable
formal multilinear series with values in `Fin n → ℂ`. -/
noncomputable def vectorOfScalarsSeries {n : ℕ} (a : ℕ → Fin n → ℂ) :
    FormalMultilinearSeries ℂ ℂ (Fin n → ℂ) :=
  FormalMultilinearSeries.pi fun i : Fin n ↦
    FormalMultilinearSeries.ofScalars ℂ (fun k ↦ a k i)

/-- Helper for Theorem I: the coordinatewise scalar packaging `vectorOfScalarsSeries a` has
coefficient sequence exactly `a`. -/
theorem vectorOfScalarsSeries_coeff {n : ℕ} (a : ℕ → Fin n → ℂ) (m : ℕ) :
    (vectorOfScalarsSeries a).coeff m = a m := by
  -- Read each coordinate from the corresponding scalar formal series.
  funext i
  change (FormalMultilinearSeries.ofScalars ℂ (fun k ↦ a k i)).coeff m = a m i
  rw [FormalMultilinearSeries.coeff_ofScalars]

/-- Helper for Theorem I: every one-variable vector-valued formal multilinear series is recovered
from its diagonal coefficient sequence. -/
theorem formalMultilinearSeries_eq_vectorOfScalarsSeries {n : ℕ}
    (P : FormalMultilinearSeries ℂ ℂ (Fin n → ℂ)) :
    P = vectorOfScalarsSeries (fun m ↦ P.coeff m) := by
  -- Equality is checked coefficientwise, and those coefficients were packaged by construction.
  ext m i
  simpa using congrArg (fun v : Fin n → ℂ ↦ v i)
    (vectorOfScalarsSeries_coeff (fun k ↦ P.coeff k) m).symm

/-- Helper for Theorem I: package the formal curve `z ↦ (z, ∑ aₖ z^k)` as a one-variable
formal multilinear series with values in `ℂ × (Fin n → ℂ)`. -/
noncomputable def recenteredCurveSeries {n : ℕ} (a : ℕ → Fin n → ℂ) :
    FormalMultilinearSeries ℂ ℂ (ℂ × (Fin n → ℂ)) :=
  (FormalMultilinearSeries.ofScalars ℂ recenteredXCoeff).prod
    (vectorOfScalarsSeries a)

/-- Helper for Cartan section27 0001_Theorem_I: pairing the identity coordinate with a centered
vector-valued one-variable owner produces the canonical recentered curve owner. -/
theorem recenteredCurve_hasFPowerSeriesAt {n : ℕ}
    {u : ℂ → Fin n → ℂ} {a : ℕ → Fin n → ℂ}
    (hu : HasFPowerSeriesAt u (vectorOfScalarsSeries a) 0) :
    HasFPowerSeriesAt (fun z : ℂ ↦ (z, u z)) (recenteredCurveSeries a) 0 := by
  -- Combine the canonical owner of the identity map with the given centered vector owner.
  have hXOwner :
      (ContinuousLinearMap.id ℂ ℂ).fpowerSeries 0 =
        FormalMultilinearSeries.ofScalars ℂ recenteredXCoeff := by
    ext m
    cases m with
    | zero =>
        simp [ContinuousLinearMap.fpowerSeries_apply_zero, recenteredXCoeff]
    | succ m =>
        cases m with
        | zero =>
            simp [ContinuousLinearMap.fpowerSeries_apply_one, recenteredXCoeff]
        | succ m =>
            simp [ContinuousLinearMap.fpowerSeries_apply_add_two, recenteredXCoeff]
  have hX :
      HasFPowerSeriesAt (fun z : ℂ ↦ z)
        (FormalMultilinearSeries.ofScalars ℂ recenteredXCoeff) 0 := by
    simpa [hXOwner, id_eq] using (ContinuousLinearMap.id ℂ ℂ).hasFPowerSeriesAt (0 : ℂ)
  simpa [recenteredCurveSeries] using hX.prod hu

/-- Helper for Theorem I: the recentered composition coefficient is the degree-`m` coefficient of
`Q` composed with the formal curve `z ↦ (z, ∑ aₖ z^k)`. -/
noncomputable def recenteredComposedCoeff {n : ℕ}
    (Q : FormalMultilinearSeries ℂ (ℂ × (Fin n → ℂ)) (Fin n → ℂ))
    (a : ℕ → Fin n → ℂ) (m : ℕ) : Fin n → ℂ :=
  (Q.comp (recenteredCurveSeries a)).coeff m

/-- Helper for Theorem I: the degree-`m` coefficient of a formal composition only depends on the
inner series coefficients through degree `m`. -/
private theorem comp_coeff_eq_of_coeff_eq_upto {F G : Type*}
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
  -- Each block in a composition of `m` has size at most `m`, so the corresponding coefficients
  -- of the inner series already agree.
  simp only [FormalMultilinearSeries.compAlongComposition_apply]
  refine congrArg (Q c.length) ?_
  funext i
  exact hPP' (c.blocksFun i) (c.blocks_le (c.blocksFun_mem_blocks i))

/-- Helper for Theorem I: matching vector coefficients through degree `m` gives the same
recentered curve coefficients through degree `m`. -/
private theorem recenteredCurveSeries_coeff_eq_of_prefix {n : ℕ}
    {a b : ℕ → Fin n → ℂ} {m : ℕ}
    (hab : ∀ k ≤ m, a k = b k) :
    ∀ k ≤ m, (recenteredCurveSeries a).coeff k = (recenteredCurveSeries b).coeff k := by
  intro k hk
  -- The `X`-component is fixed, while the `y`-component reads the matching prefix data.
  refine Prod.ext ?_ ?_
  · rfl
  · funext i
    -- Read the `i`th coordinate through the coordinatewise scalar formal series.
    calc
      ((recenteredCurveSeries a).coeff k).2 i = ((vectorOfScalarsSeries a).coeff k) i := rfl
      _ = (FormalMultilinearSeries.ofScalars ℂ (fun j ↦ a j i)).coeff k := rfl
      _ = a k i := by rw [FormalMultilinearSeries.coeff_ofScalars]
      _ = b k i := congrArg (fun u : Fin n → ℂ ↦ u i) (hab k hk)
      _ = (FormalMultilinearSeries.ofScalars ℂ (fun j ↦ b j i)).coeff k := by
            rw [FormalMultilinearSeries.coeff_ofScalars]
      _ = ((vectorOfScalarsSeries b).coeff k) i := rfl
      _ = ((recenteredCurveSeries b).coeff k).2 i := rfl

/-- Helper for Theorem I: the exact recentered composition coefficient is triangular in the
coefficient data of the recentered curve. -/
private theorem recentered_composedCoeff_eq_of_prefix {n : ℕ}
    (Q : FormalMultilinearSeries ℂ (ℂ × (Fin n → ℂ)) (Fin n → ℂ))
    {a b : ℕ → Fin n → ℂ} {m : ℕ}
    (hab : ∀ k ≤ m, a k = b k) :
    recenteredComposedCoeff Q a m = recenteredComposedCoeff Q b m := by
  -- The preceding generic composition lemma applies once the recentered curve coefficients agree
  -- through degree `m`.
  exact comp_coeff_eq_of_coeff_eq_upto
    (Q := Q) (P := recenteredCurveSeries a) (P' := recenteredCurveSeries b)
    (recenteredCurveSeries_coeff_eq_of_prefix hab)

/-- Helper for Theorem I: the exact multilinear recursion chooses the next vector coefficient
from the current recentered composition coefficient. -/
private noncomputable def formalRecenteredVectorSolutionStepCoeff {n : ℕ}
    (Q : FormalMultilinearSeries ℂ (ℂ × (Fin n → ℂ)) (Fin n → ℂ))
    (φ : PowerSeries (Fin n → ℂ)) (m : ℕ) : Fin n → ℂ :=
  ((m + 1 : ℂ)⁻¹) • recenteredComposedCoeff Q (fun k ↦ PowerSeries.coeff k φ) m

/-- Helper for Theorem I: the stage-`m` approximant records the first `m` coefficients forced by
the exact recentered multilinear recursion. -/
private noncomputable def formalRecenteredVectorSolutionApproximant {n : ℕ}
    (Q : FormalMultilinearSeries ℂ (ℂ × (Fin n → ℂ)) (Fin n → ℂ)) :
    ℕ → PowerSeries (Fin n → ℂ)
  | 0 => 0
  | m + 1 =>
      formalRecenteredVectorSolutionApproximant Q m +
        C (formalRecenteredVectorSolutionStepCoeff Q
          (formalRecenteredVectorSolutionApproximant Q m) m) * X ^ (m + 1)

/-- Helper for Theorem I: every vector approximant still has vanishing constant coefficient. -/
private theorem formal_recentered_vector_solution_approximant_constantCoeff_eq_zero {n : ℕ}
    (Q : FormalMultilinearSeries ℂ (ℂ × (Fin n → ℂ)) (Fin n → ℂ)) :
    ∀ m, PowerSeries.constantCoeff (formalRecenteredVectorSolutionApproximant Q m) = 0
  | 0 => by
      -- The initial approximant is the zero series.
      simp [formalRecenteredVectorSolutionApproximant]
  | m + 1 => by
      -- The correction term lives in degree `m + 1`, so it leaves the constant term unchanged.
      simp [formalRecenteredVectorSolutionApproximant,
        formal_recentered_vector_solution_approximant_constantCoeff_eq_zero Q m]

/-- Helper for Theorem I: once a vector coefficient has been created, the next stage does not
change it. -/
private theorem formal_recentered_vector_solution_approximant_coeff_step_eq {n : ℕ}
    (Q : FormalMultilinearSeries ℂ (ℂ × (Fin n → ℂ)) (Fin n → ℂ)) {m k : ℕ} (hmk : m ≤ k) :
    PowerSeries.coeff m (formalRecenteredVectorSolutionApproximant Q (k + 1)) =
      PowerSeries.coeff m (formalRecenteredVectorSolutionApproximant Q k) := by
  -- The recursive step only adds a monomial in degree `k + 1`.
  have hmk_ne : m ≠ k + 1 := Nat.ne_of_lt (lt_of_le_of_lt hmk (Nat.lt_succ_self k))
  rw [formalRecenteredVectorSolutionApproximant, (PowerSeries.coeff m).map_add,
    PowerSeries.coeff_C_mul_X_pow]
  simp [hmk_ne]

/-- Helper for Theorem I: before stage `m`, the `m`th vector coefficient is still zero. -/
private theorem formal_recentered_vector_solution_approximant_coeff_eq_zero_of_lt {n : ℕ}
    (Q : FormalMultilinearSeries ℂ (ℂ × (Fin n → ℂ)) (Fin n → ℂ)) :
    ∀ k m, k < m → PowerSeries.coeff m (formalRecenteredVectorSolutionApproximant Q k) = 0
  | 0, m, hm => by
      -- The zeroth approximant is the zero series.
      simp [formalRecenteredVectorSolutionApproximant]
  | k + 1, m, hm => by
      -- A stage strictly below `m` cannot yet create the `m`th coefficient.
      have hlt : k < m := lt_trans (Nat.lt_succ_self k) hm
      rw [formalRecenteredVectorSolutionApproximant, (PowerSeries.coeff m).map_add,
        PowerSeries.coeff_C_mul_X_pow]
      simp [Nat.ne_of_gt hm,
        formal_recentered_vector_solution_approximant_coeff_eq_zero_of_lt Q k m hlt]

/-- Helper for Theorem I: after stage `m`, the `m`th vector coefficient is frozen forever. -/
private theorem formal_recentered_vector_solution_approximant_stabilizes {n : ℕ}
    (Q : FormalMultilinearSeries ℂ (ℂ × (Fin n → ℂ)) (Fin n → ℂ)) (m k : ℕ) :
    PowerSeries.coeff m (formalRecenteredVectorSolutionApproximant Q (m + k)) =
      PowerSeries.coeff m (formalRecenteredVectorSolutionApproximant Q m) := by
  induction k with
  | zero =>
      simp
  | succ k ih =>
      -- Later stages add only higher-degree terms, so the `m`th coefficient persists.
      have hstep :
          PowerSeries.coeff m (formalRecenteredVectorSolutionApproximant Q (m + k + 1)) =
            PowerSeries.coeff m (formalRecenteredVectorSolutionApproximant Q (m + k)) := by
        simpa [Nat.add_assoc] using
          formal_recentered_vector_solution_approximant_coeff_step_eq
            (Q := Q) (m := m) (k := m + k) (Nat.le_add_right m k)
      calc
        PowerSeries.coeff m (formalRecenteredVectorSolutionApproximant Q (m + (k + 1)))
            = PowerSeries.coeff m (formalRecenteredVectorSolutionApproximant Q (m + k + 1)) := by
                simp [Nat.add_assoc]
        _ = PowerSeries.coeff m (formalRecenteredVectorSolutionApproximant Q (m + k)) := hstep
        _ = PowerSeries.coeff m (formalRecenteredVectorSolutionApproximant Q m) := ih

/-- Helper for Theorem I: the stage `m + 1` approximant inserts exactly the coefficient required
by the recentered multilinear recursion. -/
private theorem formal_recentered_vector_solution_approximant_next_coeff_eq {n : ℕ}
    (Q : FormalMultilinearSeries ℂ (ℂ × (Fin n → ℂ)) (Fin n → ℂ)) (m : ℕ) :
    PowerSeries.coeff (m + 1) (formalRecenteredVectorSolutionApproximant Q (m + 1)) =
      formalRecenteredVectorSolutionStepCoeff Q
        (formalRecenteredVectorSolutionApproximant Q m) m := by
  -- The new coefficient is created only at stage `m + 1`.
  rw [formalRecenteredVectorSolutionApproximant, (PowerSeries.coeff (m + 1)).map_add]
  have hzero :
      PowerSeries.coeff (m + 1) (formalRecenteredVectorSolutionApproximant Q m) = 0 := by
    exact formal_recentered_vector_solution_approximant_coeff_eq_zero_of_lt
      (Q := Q) m (m + 1) (Nat.lt_succ_self m)
  simp [hzero, formalRecenteredVectorSolutionStepCoeff]

/-- Helper for Theorem I: the stabilized coefficients define the exact formal vector solution of
the recentered multilinear recursion. -/
noncomputable def formalRecenteredVectorSolutionSeries {n : ℕ}
    (Q : FormalMultilinearSeries ℂ (ℂ × (Fin n → ℂ)) (Fin n → ℂ)) :
    PowerSeries (Fin n → ℂ) :=
  PowerSeries.mk fun m ↦
    PowerSeries.coeff m (formalRecenteredVectorSolutionApproximant Q m)

/-- Helper for Theorem I: the stabilized vector series agrees with the `m`th approximant through
degree `m`. -/
private theorem formal_recentered_vector_solution_series_coeff_eq_approximant {n : ℕ}
    (Q : FormalMultilinearSeries ℂ (ℂ × (Fin n → ℂ)) (Fin n → ℂ)) {m k : ℕ} (hmk : m ≤ k) :
    PowerSeries.coeff m (formalRecenteredVectorSolutionSeries Q) =
      PowerSeries.coeff m (formalRecenteredVectorSolutionApproximant Q k) := by
  -- Read the coefficient from stage `m`, then use stabilization to move to any later stage.
  calc
    PowerSeries.coeff m (formalRecenteredVectorSolutionSeries Q)
        = PowerSeries.coeff m (formalRecenteredVectorSolutionApproximant Q m) := by
            simp [formalRecenteredVectorSolutionSeries]
    _ = PowerSeries.coeff m (formalRecenteredVectorSolutionApproximant Q (m + (k - m))) := by
          symm
          exact formal_recentered_vector_solution_approximant_stabilizes (Q := Q) m (k - m)
    _ = PowerSeries.coeff m (formalRecenteredVectorSolutionApproximant Q k) := by
          rw [Nat.add_sub_of_le hmk]

/-- Helper for Theorem I: the exact recentered multilinear coefficient recursion has a unique
formal vector-valued power-series solution. -/
theorem formalRecenteredVectorSolutionSeries_isSolution {n : ℕ}
    (Q : FormalMultilinearSeries ℂ (ℂ × (Fin n → ℂ)) (Fin n → ℂ)) :
    PowerSeries.constantCoeff (formalRecenteredVectorSolutionSeries Q) = 0 ∧
      ∀ m, PowerSeries.coeff (m + 1) (formalRecenteredVectorSolutionSeries Q) =
        ((m + 1 : ℂ)⁻¹) •
          recenteredComposedCoeff Q
            (fun k ↦ PowerSeries.coeff k (formalRecenteredVectorSolutionSeries Q)) m := by
  -- Read the stabilized series from the recursive approximants, then compare prefixes to the
  -- exact multilinear recursion.
  let φ : PowerSeries (Fin n → ℂ) := formalRecenteredVectorSolutionSeries Q
  have hφ0 : PowerSeries.constantCoeff φ = 0 := by
    -- The constant coefficient is inherited from the zeroth approximant, namely the zero series.
    have hcoeff0 : PowerSeries.coeff 0 φ = 0 := by
      simp [φ, formalRecenteredVectorSolutionSeries,
        formalRecenteredVectorSolutionApproximant]
    simpa [PowerSeries.coeff_zero_eq_constantCoeff_apply] using hcoeff0
  have hφrec :
      ∀ m, PowerSeries.coeff (m + 1) φ =
        ((m + 1 : ℂ)⁻¹) • recenteredComposedCoeff Q (fun k ↦ PowerSeries.coeff k φ) m := by
    intro m
    have hprefix :
        ∀ k ≤ m,
          PowerSeries.coeff k (formalRecenteredVectorSolutionApproximant Q m) =
            PowerSeries.coeff k φ := by
      intro k hk
      symm
      exact formal_recentered_vector_solution_series_coeff_eq_approximant
        (Q := Q) (m := k) (k := m) hk
    calc
      PowerSeries.coeff (m + 1) φ
          = PowerSeries.coeff (m + 1) (formalRecenteredVectorSolutionApproximant Q (m + 1)) := by
              exact formal_recentered_vector_solution_series_coeff_eq_approximant
                (Q := Q) (m := m + 1) (k := m + 1) le_rfl
      _ = formalRecenteredVectorSolutionStepCoeff Q
            (formalRecenteredVectorSolutionApproximant Q m) m := by
              exact formal_recentered_vector_solution_approximant_next_coeff_eq (Q := Q) m
      _ = ((m + 1 : ℂ)⁻¹) • recenteredComposedCoeff Q (fun k ↦ PowerSeries.coeff k φ) m := by
            have hcomp :
                recenteredComposedCoeff Q
                    (fun k ↦
                      PowerSeries.coeff k (formalRecenteredVectorSolutionApproximant Q m)) m =
                  recenteredComposedCoeff Q (fun k ↦ PowerSeries.coeff k φ) m :=
              recentered_composedCoeff_eq_of_prefix Q hprefix
            simpa [formalRecenteredVectorSolutionStepCoeff] using
              congrArg (fun v : Fin n → ℂ ↦ ((m + 1 : ℂ)⁻¹) • v) hcomp
  simpa [φ] using And.intro hφ0 hφrec

/-- Helper for Theorem I: the exact recentered multilinear coefficient recursion has a unique
formal vector-valued power-series solution. -/
theorem existsUnique_formal_series_solution_for_recentered_multilinear_system {n : ℕ}
    (Q : FormalMultilinearSeries ℂ (ℂ × (Fin n → ℂ)) (Fin n → ℂ)) :
    ∃! φ : PowerSeries (Fin n → ℂ),
      PowerSeries.constantCoeff φ = 0 ∧
      ∀ m, PowerSeries.coeff (m + 1) φ =
        ((m + 1 : ℂ)⁻¹) • recenteredComposedCoeff Q (fun k ↦ PowerSeries.coeff k φ) m := by
  -- Route correction: solve the exact multilinear coefficient recursion first, before any
  -- analytic realization or majorant argument.
  refine ⟨formalRecenteredVectorSolutionSeries Q,
    formalRecenteredVectorSolutionSeries_isSolution (Q := Q), ?_⟩
  intro ψ hψ
  rcases hψ with ⟨hψ0, hψrec⟩
  have hφ :=
    formalRecenteredVectorSolutionSeries_isSolution (Q := Q)
  rcases hφ with ⟨hφ0, hφrec⟩
  let φ : PowerSeries (Fin n → ℂ) := formalRecenteredVectorSolutionSeries Q
  -- Compare coefficients inductively: the next coefficient is forced by the common prefix.
  have hcoeff :
      ∀ d, ∀ k ≤ d, PowerSeries.coeff k φ = PowerSeries.coeff k ψ := by
    intro d
    induction d with
    | zero =>
        intro k hk
        have hk0 : k = 0 := Nat.eq_zero_of_le_zero hk
        subst hk0
        simpa [PowerSeries.coeff_zero_eq_constantCoeff_apply] using hφ0.trans hψ0.symm
    | succ d ih =>
        intro k hk
        by_cases hkd : k ≤ d
        · exact ih k hkd
        · have hk_eq : k = d + 1 := by omega
          subst hk_eq
          have hcomp :
              recenteredComposedCoeff Q (fun m ↦ PowerSeries.coeff m φ) d =
                recenteredComposedCoeff Q (fun m ↦ PowerSeries.coeff m ψ) d :=
            recentered_composedCoeff_eq_of_prefix Q (fun m hm ↦ ih m hm)
          calc
            PowerSeries.coeff (d + 1) φ
                =
                  ((d + 1 : ℂ)⁻¹) •
                    recenteredComposedCoeff Q (fun k ↦ PowerSeries.coeff k φ) d := by
                    rw [hφrec d]
            _ = ((d + 1 : ℂ)⁻¹) • recenteredComposedCoeff Q (fun k ↦ PowerSeries.coeff k ψ) d := by
                  exact congrArg (fun v : Fin n → ℂ ↦ ((d + 1 : ℂ)⁻¹) • v) hcomp
            _ = PowerSeries.coeff (d + 1) ψ := by
                  rw [hψrec d]
  ext m i
  exact (congrArg (fun v : Fin n → ℂ ↦ v i) (hcoeff m m le_rfl)).symm
