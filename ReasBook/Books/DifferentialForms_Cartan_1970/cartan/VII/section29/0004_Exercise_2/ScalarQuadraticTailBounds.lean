import DifferentialForms_Cartan_1970.cartan.VII.section29.«0004_Exercise_2».CoefficientwiseMajorantPropagation

open scoped BigOperators MvPowerSeries PowerSeries MvPowerSeries.WithPiTopology
open PowerSeries

universe u

section ScalarQuadraticMajorantExistence

variable {𝕜 : Type u} [NormedCommRing 𝕜]
variable {n p : ℕ}

/-- Helper for Cartan section29 0004_Exercise_2: scaling the `NNReal`-valued majorant by a real
constant commutes with taking powers coefficientwise. -/
lemma coeff_scaledMajorantPow
    (a : ℝ)
    (A : MvPowerSeries (ParamIndex n p) NNReal)
    (q : ℕ) (d : ParamIndex n p →₀ ℕ) :
    MvPowerSeries.coeff d
      ((MvPowerSeries.C a * MvPowerSeries.map NNReal.toRealHom A) ^ q) =
      a ^ q * (((MvPowerSeries.coeff d (A ^ q) : NNReal) : ℝ)) := by
  induction q generalizing d with
  | zero =>
      by_cases hd : d = 0
      · subst hd
        simp
      · simp [MvPowerSeries.coeff_one, hd]
  | succ q ih =>
    rw [pow_succ, pow_succ, MvPowerSeries.coeff_mul]
    simp_rw [MvPowerSeries.coeff_C_mul, MvPowerSeries.coeff_map, ih]
    calc
      ∑ i ∈ Finset.antidiagonal d,
          a ^ q * ↑((MvPowerSeries.coeff i.1) (A ^ q)) *
            (a * NNReal.toRealHom ((MvPowerSeries.coeff i.2) A)) =
        a ^ q *
          ∑ i ∈ Finset.antidiagonal d,
            ↑((MvPowerSeries.coeff i.1) (A ^ q)) *
              (a * NNReal.toRealHom ((MvPowerSeries.coeff i.2) A)) := by
              simp_rw [mul_assoc]
              rw [← Finset.mul_sum]
      _ = a ^ q * (a * ↑((MvPowerSeries.coeff d) (A ^ (q + 1)))) := by
            congr 1
            calc
              ∑ i ∈ Finset.antidiagonal d,
                  ↑((MvPowerSeries.coeff i.1) (A ^ q)) *
                    (a * NNReal.toRealHom ((MvPowerSeries.coeff i.2) A)) =
                a * ∑ i ∈ Finset.antidiagonal d,
                    ↑(((MvPowerSeries.coeff i.1) (A ^ q)) * ((MvPowerSeries.coeff i.2) A)) := by
                      calc
                        ∑ i ∈ Finset.antidiagonal d,
                            ↑((MvPowerSeries.coeff i.1) (A ^ q)) *
                              (a * NNReal.toRealHom ((MvPowerSeries.coeff i.2) A)) =
                        ∑ i ∈ Finset.antidiagonal d,
                            a * ↑(((MvPowerSeries.coeff i.1) (A ^ q)) *
                              ((MvPowerSeries.coeff i.2) A)) := by
                                refine Finset.sum_congr rfl ?_
                                intro i hi
                                norm_num [mul_assoc, mul_left_comm, mul_comm]
                        _ = a * ∑ i ∈ Finset.antidiagonal d,
                              ↑(((MvPowerSeries.coeff i.1) (A ^ q)) *
                                ((MvPowerSeries.coeff i.2) A)) := by
                                  rw [← Finset.mul_sum]
              _ = a * ↑((MvPowerSeries.coeff d) (A ^ q * A)) := by
                    congr 1
                    rw [MvPowerSeries.coeff_mul]
                    norm_num
              _ = a * ↑((MvPowerSeries.coeff d) (A ^ (q + 1))) := by
                    simp [pow_succ]
      _ = a ^ q * a * ↑((MvPowerSeries.coeff d) (A ^ (q + 1))) := by
            ring

/-- Helper for Cartan section29 0004_Exercise_2: the finite owner sum of the scalar power terms
that survive in the nonlinear majorant up to total parameter degree `N`. -/
noncomputable def scaledMajorantPowersSum
    (a : ℝ)
    (A : MvPowerSeries (ParamIndex n p) NNReal)
    (N : ℕ) : MvPowerSeries (ParamIndex n p) ℝ :=
  Finset.sum (Finset.Icc 2 N) fun qx =>
    ((MvPowerSeries.C a * MvPowerSeries.map NNReal.toRealHom A) ^ qx)

/-- Helper for Cartan section29 0004_Exercise_2: every coefficient of the outer geometric
majorant factor is nonnegative. Pure `z` coefficients are bounded from below by
`outerCoeff_pureZ_lower`, and mixed coefficients vanish because the series is a pure-`z` rename. -/
lemma outerCoeff_nonneg
    (M R : NNReal)
    (e : ParamIndex n p →₀ ℕ) :
    0 ≤
      MvPowerSeries.coeff e
        ((MvPowerSeries.C (M : ℝ)) *
          (1 - MvPowerSeries.C ((R : ℝ)⁻¹) * paramZSum (n := n) (p := p))⁻¹) := by
  by_cases he : e ∈ Set.range (Finsupp.embDomain paramZEmb)
  · rcases he with ⟨ez, rfl⟩
    exact le_trans (by positivity) (outerCoeff_pureZ_lower (n := n) M R ez)
  · have he' : e ∉ Set.range (Finsupp.mapDomain paramZEmb) := by
      simpa [Finsupp.embDomain_eq_mapDomain] using he
    have hzero :
        MvPowerSeries.coeff e
            ((MvPowerSeries.C (M : ℝ)) *
              (1 - MvPowerSeries.C ((R : ℝ)⁻¹) * paramZSum (n := n) (p := p))⁻¹) = 0 := by
      rw [outerFactor_eq_rename (n := n) M R]
      exact MvPowerSeries.coeff_rename_eq_zero
        (f := paramZEmb)
        (p := (MvPowerSeries.C (M : ℝ)) *
          (1 - MvPowerSeries.C ((R : ℝ)⁻¹) *
              ∑ k : Fin p, (MvPowerSeries.X k : MvPowerSeries (Fin p) ℝ))⁻¹)
        he'
    simp [hzero]

/-- Helper for Cartan section29 0004_Exercise_2: the scalar power terms built from the `NNReal`
majorant have coefficientwise nonnegative real coefficients. -/
lemma coeffScaledMajorantPow_nonneg
    (a : ℝ)
    (ha : 0 ≤ a)
    (A : MvPowerSeries (ParamIndex n p) NNReal)
    (q : ℕ) (e : ParamIndex n p →₀ ℕ) :
    0 ≤
      MvPowerSeries.coeff e
        ((MvPowerSeries.C a * MvPowerSeries.map NNReal.toRealHom A) ^ q) := by
  rw [coeff_scaledMajorantPow (n := n) (p := p) a A q e]
  exact mul_nonneg (pow_nonneg ha q) (by positivity)

/-- Helper for Cartan section29 0004_Exercise_2: if the scalar power exponent already exceeds the
target total parameter degree, then the corresponding coefficient of
`outer * ((C a * map A)^q)` vanishes. This isolates the order argument before the final
higher-majorant comparison. -/
lemma coeffOuterMulScaledMajorantPow_eq_zero_of_paramDegree_lt
    (outer : MvPowerSeries (ParamIndex n p) ℝ)
    (a : ℝ)
    {A : MvPowerSeries (ParamIndex n p) NNReal}
    (hA0 : MvPowerSeries.constantCoeff A = 0)
    (q : ℕ) (d : ParamIndex n p →₀ ℕ)
    (hq : paramDegree d < q) :
    MvPowerSeries.coeff d
      (outer *
        ((MvPowerSeries.C a * MvPowerSeries.map NNReal.toRealHom A) ^ q)) = 0 := by
  classical
  have hscaled0 :
      MvPowerSeries.constantCoeff
          (MvPowerSeries.C a * MvPowerSeries.map NNReal.toRealHom A) = 0 := by
    simp [MvPowerSeries.constantCoeff_map, hA0]
  rw [MvPowerSeries.coeff_mul]
  apply Finset.sum_eq_zero
  intro e he
  have hsum : e.1 + e.2 = d := Finset.mem_antidiagonal.mp he
  have hdeg :
      paramDegree e.1 + paramDegree e.2 = paramDegree d := by
    rw [← hsum]
    simp [paramDegree, Finset.sum_add_distrib]
  have hdegle : paramDegree e.2 ≤ paramDegree d := by
    omega
  have hlt : paramDegree e.2 < q := lt_of_le_of_lt hdegle hq
  have hlt' : ((paramDegree e.2 : ℕ) : ℕ∞) < q := by
    exact_mod_cast hlt
  have hzero :
      MvPowerSeries.coeff e.2
        ((MvPowerSeries.C a * MvPowerSeries.map NNReal.toRealHom A) ^ q) = 0 := by
    apply MvPowerSeries.coeff_of_lt_order
    simpa [paramDegree_eq_degree] using
      (lt_of_lt_of_le hlt'
        (MvPowerSeries.le_order_pow_of_constantCoeff_eq_zero q hscaled0))
  simp [hzero]

/-- Helper for Cartan section29 0004_Exercise_2: coefficient equality of the right factor below
the target total degree is enough to identify the degree-`d` coefficient after multiplying by a
fixed left factor. -/
lemma coeffMul_eq_of_rightCoeffEqWithin
    (φ ψ θ : MvPowerSeries (ParamIndex n p) ℝ)
    (d : ParamIndex n p →₀ ℕ)
    (hψθ : ∀ e, paramDegree e ≤ paramDegree d →
      MvPowerSeries.coeff e ψ = MvPowerSeries.coeff e θ) :
    MvPowerSeries.coeff d (φ * ψ) =
      MvPowerSeries.coeff d (φ * θ) := by
  classical
  rw [MvPowerSeries.coeff_mul, MvPowerSeries.coeff_mul]
  refine Finset.sum_congr rfl ?_
  intro e he
  have hsum : e.1 + e.2 = d := Finset.mem_antidiagonal.mp he
  have hdeg :
      paramDegree e.1 + paramDegree e.2 = paramDegree d := by
    rw [← hsum]
    simp [paramDegree, Finset.sum_add_distrib]
  have hle : paramDegree e.2 ≤ paramDegree d := by
    omega
  simp [hψθ e.2 hle]

/-- Helper for Cartan section29 0004_Exercise_2: below a fixed target degree, the cancelled
quadratic tail is coefficientwise equal to the finite sum of its power terms indexed by
`qx ∈ [2, paramDegree d]`. This is the owner-level bridge needed for the higher slice
comparison. -/
lemma coeffScalarQuadraticTail_eq_scaledMajorantPowersSumWithin
    (a : ℝ)
    {A : MvPowerSeries (ParamIndex n p) NNReal}
    (hA0 : MvPowerSeries.constantCoeff A = 0)
    (d : ParamIndex n p →₀ ℕ)
    (e : ParamIndex n p →₀ ℕ)
    (hle : paramDegree e ≤ paramDegree d) :
    MvPowerSeries.coeff e (scalarQuadraticTail (n := n) (p := p) a A) =
      MvPowerSeries.coeff e
        (scaledMajorantPowersSum (n := n) (p := p) a A (paramDegree d)) :=
    -- Repackage the scalar support-file cutoff bridge through the local owner abbreviation
    -- `scaledMajorantPowersSum`.
    by
      simpa [scaledMajorantPowersSum] using
        coeffScalarQuadraticTail_eq_sum_IccWithin (n := n) (p := p) a hA0 d e hle

/-- Helper for Cartan section29 0004_Exercise_2: the coefficient of the nonlinear scalar
majorant `outer * scalarQuadraticTail` at total degree `d` is the finite sum of the owner-form
coefficients `coeff d (outer * ((C a * map A)^qx))` for `qx ∈ [2, paramDegree d]`. -/
lemma coeffHigherMajorant_eq_sum_Icc
    (outer : MvPowerSeries (ParamIndex n p) ℝ)
    (a : ℝ)
    {A : MvPowerSeries (ParamIndex n p) NNReal}
    (hA0 : MvPowerSeries.constantCoeff A = 0)
    (d : ParamIndex n p →₀ ℕ) :
    MvPowerSeries.coeff d
      (outer * scalarQuadraticTail (n := n) (p := p) a A) =
        Finset.sum (Finset.Icc 2 (paramDegree d)) fun qx =>
          MvPowerSeries.coeff d
            (outer *
              ((MvPowerSeries.C a * MvPowerSeries.map NNReal.toRealHom A) ^ qx)) :=
    by
      -- Transport the finite cutoff normalization through the fixed outer factor before
      -- distributing the coefficient over the owner sum.
      have htail :
          MvPowerSeries.coeff d
              (outer * scalarQuadraticTail (n := n) (p := p) a A) =
            MvPowerSeries.coeff d
              (outer * scaledMajorantPowersSum (n := n) (p := p) a A (paramDegree d)) := by
        refine coeffMul_eq_of_rightCoeffEqWithin (n := n) (p := p)
          outer
          (scalarQuadraticTail (n := n) (p := p) a A)
          (scaledMajorantPowersSum (n := n) (p := p) a A (paramDegree d))
          d ?_
        intro e he
        exact coeffScalarQuadraticTail_eq_scaledMajorantPowersSumWithin
          (n := n) (p := p) a hA0 d e he
      calc
        MvPowerSeries.coeff d
            (outer * scalarQuadraticTail (n := n) (p := p) a A) =
          MvPowerSeries.coeff d
            (outer * scaledMajorantPowersSum (n := n) (p := p) a A (paramDegree d)) :=
          htail
        _ = MvPowerSeries.coeff d
              (Finset.sum (Finset.Icc 2 (paramDegree d)) fun qx =>
                outer *
                  ((MvPowerSeries.C a * MvPowerSeries.map NNReal.toRealHom A) ^ qx)) := by
              simp [scaledMajorantPowersSum, Finset.mul_sum]
        _ = Finset.sum (Finset.Icc 2 (paramDegree d)) fun qx =>
              MvPowerSeries.coeff d
                (outer *
                  ((MvPowerSeries.C a * MvPowerSeries.map NNReal.toRealHom A) ^ qx)) := by
              simp

/-- Helper for Cartan section29 0004_Exercise_2: the outer geometric factor in the scalar
majorant operator. Naming it once keeps the later transport lemmas in a stable normal form. -/
noncomputable def scalarOuterFactor
    (M R : NNReal) : MvPowerSeries (ParamIndex n p) ℝ :=
  (MvPowerSeries.C (M : ℝ)) *
    (1 - MvPowerSeries.C ((R : ℝ)⁻¹) * paramZSum (n := n) (p := p))⁻¹

/-- Helper for Cartan section29 0004_Exercise_2: the `qx`-th owner-side power term in the
nonlinear scalar majorant comparison. -/
noncomputable def scaledMajorantPower
    (a : ℝ)
    (A : MvPowerSeries (ParamIndex n p) NNReal)
    (qx : ℕ) : MvPowerSeries (ParamIndex n p) ℝ :=
  (MvPowerSeries.C a * MvPowerSeries.map NNReal.toRealHom A) ^ qx

/-- Helper for Cartan section29 0004_Exercise_2: for coefficientwise nonnegative factors, a
single antidiagonal summand gives a lower bound for the corresponding coefficient of the
product. This is the owner-side coefficient-of-product bridge used later for the scalar majorant
transport. -/
lemma coeffMul_ge_antidiagonalTerm
    (outer scaled : MvPowerSeries (ParamIndex n p) ℝ)
    (d shift : ParamIndex n p →₀ ℕ)
    (hshift : shift ≤ d)
    (houter : ∀ e, 0 ≤ MvPowerSeries.coeff e outer)
    (hscaled : ∀ e, 0 ≤ MvPowerSeries.coeff e scaled) :
    MvPowerSeries.coeff shift outer *
      MvPowerSeries.coeff (d - shift) scaled ≤
      MvPowerSeries.coeff d (outer * scaled) := by
  have hmem : (shift, d - shift) ∈ Finset.antidiagonal d := by
    exact Finset.mem_antidiagonal.mpr (add_tsub_cancel_of_le hshift)
  have hnonneg :
      ∀ e ∈ Finset.antidiagonal d,
        0 ≤ MvPowerSeries.coeff e.1 outer * MvPowerSeries.coeff e.2 scaled := by
    intro e he
    exact mul_nonneg (houter e.1) (hscaled e.2)
  -- Keep the chosen antidiagonal term and compare it with the whole product coefficient.
  rw [MvPowerSeries.coeff_mul]
  simpa using
    (Finset.single_le_sum hnonneg hmem :
      MvPowerSeries.coeff shift outer * MvPowerSeries.coeff (d - shift) scaled ≤
        ∑ e ∈ Finset.antidiagonal d,
          MvPowerSeries.coeff e.1 outer * MvPowerSeries.coeff e.2 scaled)

/-- Helper for Cartan section29 0004_Exercise_2: a fixed finite fiber of higher monomials with
`x`-degree `qx` and pure-`z` part `ez` is bounded by the explicit shifted coefficient of `A ^ qx`
weighted by the source majorant factor `M R^{-(qx + |ez|)}`. -/
lemma higherSubstFiber_le_weightedShiftedCoeff
    (S : RecursiveImplicitSystem 𝕜 n p)
    (M R : NNReal) (hS : S.IsMajorizedBy M R)
    {φ : Fin n → MvPowerSeries (ParamIndex n p) 𝕜}
    {A : MvPowerSeries (ParamIndex n p) NNReal}
    (hφ0 : ∀ j, MvPowerSeries.constantCoeff (φ j) = 0)
    (j : Fin n) (d : ParamIndex n p →₀ ℕ)
    (hA : ∀ j' e, paramDegree e < paramDegree d →
      ‖MvPowerSeries.coeff e (φ j')‖ ≤ (((MvPowerSeries.coeff e A : NNReal) : ℝ)))
    (qx : ℕ) (ez : Fin p →₀ ℕ)
    (t : Finset ((Fin n ⊕ Fin p) →₀ ℕ))
    (hqx : 2 ≤ qx)
    (ht :
      ∀ m ∈ t,
        xDegree m = qx ∧
          Finsupp.comapDomain Sum.inr m Sum.inr_injective.injOn = ez) :
    Finset.sum t (fun m ↦
      ‖MvPowerSeries.coeff m (S.higher j) *
          MvPowerSeries.coeff d
            (m.prod fun s q ↦ (solutionSubst φ (higherToSystem s)) ^ q)‖) ≤
      if Finsupp.embDomain paramZEmb ez ≤ d then
        (M : ℝ) * (R : ℝ)⁻¹ ^ (qx + ∑ k : Fin p, ez k) *
          (((MvPowerSeries.coeff
              (d - Finsupp.embDomain paramZEmb ez) (A ^ qx) : NNReal) : ℝ))
      else
        0 := by
  let shift : ParamIndex n p →₀ ℕ := Finsupp.embDomain paramZEmb ez
  by_cases hshift : shift ≤ d
  · let coeffA : ℝ := (((MvPowerSeries.coeff (d - shift) (A ^ qx) : NNReal) : ℝ))
    have hcoeffBound :
        ∀ m ∈ t,
          ‖MvPowerSeries.coeff d
              (m.prod fun s q ↦ (solutionSubst φ (higherToSystem s)) ^ q)‖ ≤
            coeffA := by
      intro m hm
      rcases ht m hm with ⟨hmx, hmz⟩
      -- Rewrite the generic higher-monomial coefficient bound in the fixed fiber normal form.
      simpa [shift, coeffA, hshift, hmx, hmz] using
        (coeffSolutionSubstHigherMonomial_norm_le_ofCoeffLe
          (n := n) (p := p) (d := d) (φ := φ) (A := A) hφ0 hA m (by simpa [hmx] using hqx))
    have hterm :
        ∀ m ∈ t,
          ‖MvPowerSeries.coeff m (S.higher j) *
              MvPowerSeries.coeff d
                (m.prod fun s q ↦ (solutionSubst φ (higherToSystem s)) ^ q)‖ ≤
            ‖MvPowerSeries.coeff m (S.higher j)‖ * coeffA := by
      intro m hm
      -- Isolate the fixed shifted coefficient factor so the source slice sum can be reused.
      calc
        ‖MvPowerSeries.coeff m (S.higher j) *
            MvPowerSeries.coeff d
              (m.prod fun s q ↦ (solutionSubst φ (higherToSystem s)) ^ q)‖ ≤
          ‖MvPowerSeries.coeff m (S.higher j)‖ *
            ‖MvPowerSeries.coeff d
                (m.prod fun s q ↦ (solutionSubst φ (higherToSystem s)) ^ q)‖ := by
              exact norm_mul_le _ _
        _ ≤ ‖MvPowerSeries.coeff m (S.higher j)‖ * coeffA := by
              exact mul_le_mul_of_nonneg_left (hcoeffBound m hm) (norm_nonneg _)
    have hslice :
        Finset.sum t (fun m ↦ ‖MvPowerSeries.coeff m (S.higher j)‖) ≤
          (M : ℝ) * (R : ℝ)⁻¹ ^ (qx + ∑ k : Fin p, ez k) := by
      exact higherCoeffFiber_sum_le_majorantSlice (n := n) (p := p) S M R hS j ez qx t hqx ht
    calc
      Finset.sum t (fun m ↦
          ‖MvPowerSeries.coeff m (S.higher j) *
              MvPowerSeries.coeff d
                (m.prod fun s q ↦ (solutionSubst φ (higherToSystem s)) ^ q)‖) ≤
        Finset.sum t (fun m ↦ ‖MvPowerSeries.coeff m (S.higher j)‖ * coeffA) := by
          exact Finset.sum_le_sum hterm
      _ = coeffA * Finset.sum t (fun m ↦ ‖MvPowerSeries.coeff m (S.higher j)‖) := by
          calc
            Finset.sum t (fun m ↦ ‖MvPowerSeries.coeff m (S.higher j)‖ * coeffA) =
                Finset.sum t (fun m ↦ coeffA * ‖MvPowerSeries.coeff m (S.higher j)‖) := by
                  refine Finset.sum_congr rfl ?_
                  intro m hm
                  ring
            _ = coeffA * Finset.sum t (fun m ↦ ‖MvPowerSeries.coeff m (S.higher j)‖) := by
                  rw [Finset.mul_sum]
      _ ≤ coeffA * ((M : ℝ) * (R : ℝ)⁻¹ ^ (qx + ∑ k : Fin p, ez k)) := by
          exact mul_le_mul_of_nonneg_left hslice (by positivity)
      _ = (M : ℝ) * (R : ℝ)⁻¹ ^ (qx + ∑ k : Fin p, ez k) * coeffA := by
          ac_rfl
      _ = if shift ≤ d then
            (M : ℝ) * (R : ℝ)⁻¹ ^ (qx + ∑ k : Fin p, ez k) *
              (((MvPowerSeries.coeff (d - shift) (A ^ qx) : NNReal) : ℝ))
          else
            0 := by
              simp [shift, coeffA, hshift]
  · have hcoeffZero :
        ∀ m ∈ t,
          ‖MvPowerSeries.coeff d
              (m.prod fun s q ↦ (solutionSubst φ (higherToSystem s)) ^ q)‖ ≤ 0 := by
      intro m hm
      rcases ht m hm with ⟨hmx, hmz⟩
      -- In the impossible-shift branch, every substituted higher monomial contributes zero at
      -- degree `d`.
      simpa [shift, hshift, hmx, hmz] using
        (coeffSolutionSubstHigherMonomial_norm_le_ofCoeffLe
          (n := n) (p := p) (d := d) (φ := φ) (A := A) hφ0 hA m (by simpa [hmx] using hqx))
    have hterm :
        ∀ m ∈ t,
          ‖MvPowerSeries.coeff m (S.higher j) *
              MvPowerSeries.coeff d
                (m.prod fun s q ↦ (solutionSubst φ (higherToSystem s)) ^ q)‖ ≤ 0 := by
      intro m hm
      calc
        ‖MvPowerSeries.coeff m (S.higher j) *
            MvPowerSeries.coeff d
              (m.prod fun s q ↦ (solutionSubst φ (higherToSystem s)) ^ q)‖ ≤
          ‖MvPowerSeries.coeff m (S.higher j)‖ *
            ‖MvPowerSeries.coeff d
                (m.prod fun s q ↦ (solutionSubst φ (higherToSystem s)) ^ q)‖ := by
              exact norm_mul_le _ _
        _ ≤ ‖MvPowerSeries.coeff m (S.higher j)‖ * 0 := by
              exact mul_le_mul_of_nonneg_left (hcoeffZero m hm) (norm_nonneg _)
        _ = 0 := by simp
    calc
      Finset.sum t (fun m ↦
          ‖MvPowerSeries.coeff m (S.higher j) *
              MvPowerSeries.coeff d
                (m.prod fun s q ↦ (solutionSubst φ (higherToSystem s)) ^ q)‖) ≤
        Finset.sum t (fun _ ↦ (0 : ℝ)) := by
          exact Finset.sum_le_sum hterm
      _ = if shift ≤ d then
            (M : ℝ) * (R : ℝ)⁻¹ ^ (qx + ∑ k : Fin p, ez k) *
              (((MvPowerSeries.coeff (d - shift) (A ^ qx) : NNReal) : ℝ))
          else
            0 := by
              simp [shift, hshift]

/-- Helper for Cartan section29 0004_Exercise_2: for one fixed pure-`z` shift, the explicit
source-side weight is bounded by the corresponding chosen antidiagonal summand in the owner-side
product coefficient. -/
lemma pureZWeightMul_shiftedCoeff_le_antidiagonalTerm
    (M R : NNReal)
    {A : MvPowerSeries (ParamIndex n p) NNReal}
    (qx : ℕ) (ez : Fin p →₀ ℕ)
    (d : ParamIndex n p →₀ ℕ)
    (hn : 1 ≤ n) :
    (M : ℝ) * (R : ℝ)⁻¹ ^ (qx + ∑ k : Fin p, ez k) *
      (((MvPowerSeries.coeff
          (d - Finsupp.embDomain paramZEmb ez) (A ^ qx) : NNReal) : ℝ)) ≤
      MvPowerSeries.coeff (Finsupp.embDomain paramZEmb ez)
          (scalarOuterFactor (n := n) (p := p) M R) *
        MvPowerSeries.coeff
          (d - Finsupp.embDomain paramZEmb ez)
          (scaledMajorantPower (n := n) (p := p) ((((n : ℕ) : ℝ) / (R : ℝ))) A qx) := by
  let shift : ParamIndex n p →₀ ℕ := Finsupp.embDomain paramZEmb ez
  let a : ℝ := (((n : ℕ) : ℝ) / (R : ℝ))
  let coeffA : ℝ := (((MvPowerSeries.coeff (d - shift) (A ^ qx) : NNReal) : ℝ))
  let qz : ℕ := ∑ k : Fin p, ez k
  have houter :
      (M : ℝ) * (R : ℝ)⁻¹ ^ qz ≤
        MvPowerSeries.coeff shift (scalarOuterFactor (n := n) (p := p) M R) := by
    simpa [shift, qz, scalarOuterFactor] using
      (outerCoeff_pureZ_lower (n := n) (p := p) M R ez)
  have hbase :
      (R : ℝ)⁻¹ ≤ a := by
    have hn' : (1 : ℝ) ≤ ((n : ℕ) : ℝ) := by
      exact_mod_cast hn
    simpa [a, div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using
      (mul_le_mul_of_nonneg_right hn' (show 0 ≤ (R : ℝ)⁻¹ by positivity) :
        1 * (R : ℝ)⁻¹ ≤ ((n : ℕ) : ℝ) * (R : ℝ)⁻¹)
  have hpow :
      (R : ℝ)⁻¹ ^ qx ≤ a ^ qx := by
    gcongr
  have hscaled :
      (R : ℝ)⁻¹ ^ qx * coeffA ≤
        MvPowerSeries.coeff (d - shift)
          (scaledMajorantPower (n := n) (p := p) a A qx) := by
    rw [scaledMajorantPower, coeff_scaledMajorantPow (n := n) (p := p) a A qx (d - shift)]
    exact (mul_le_mul_of_nonneg_right hpow (by positivity : 0 ≤ coeffA)).trans_eq (by rfl)
  have houter_nonneg :
      0 ≤ MvPowerSeries.coeff shift (scalarOuterFactor (n := n) (p := p) M R) := by
    exact outerCoeff_nonneg (n := n) (p := p) M R shift
  calc
    (M : ℝ) * (R : ℝ)⁻¹ ^ (qx + ∑ k : Fin p, ez k) * coeffA =
      ((M : ℝ) * (R : ℝ)⁻¹ ^ qz) * (((R : ℝ)⁻¹ ^ qx) * coeffA) := by
        rw [pow_add]
        ac_rfl
    _ ≤ MvPowerSeries.coeff shift (scalarOuterFactor (n := n) (p := p) M R) *
          MvPowerSeries.coeff (d - shift)
            (scaledMajorantPower (n := n) (p := p) a A qx) := by
        exact mul_le_mul houter hscaled (by positivity) houter_nonneg

/-- Helper for Cartan section29 0004_Exercise_2: summing the weighted shifted coefficients over a
finite family of pure-`z` shifts stays below the corresponding owner-side product coefficient,
because the chosen antidiagonal summands are distinct and all coefficients are nonnegative. -/
lemma weightedShiftedCoeffSum_le_outerMulScaledMajorantPowCoeff
    (M R : NNReal)
    {A : MvPowerSeries (ParamIndex n p) NNReal}
    (qx : ℕ)
    (E : Finset (Fin p →₀ ℕ))
    (d : ParamIndex n p →₀ ℕ)
    (hn : 1 ≤ n) :
    Finset.sum E (fun ez ↦
      if Finsupp.embDomain paramZEmb ez ≤ d then
        (M : ℝ) * (R : ℝ)⁻¹ ^ (qx + ∑ k : Fin p, ez k) *
          (((MvPowerSeries.coeff
              (d - Finsupp.embDomain paramZEmb ez) (A ^ qx) : NNReal) : ℝ))
      else
        0) ≤
      MvPowerSeries.coeff d
        (scalarOuterFactor (n := n) (p := p) M R *
          scaledMajorantPower (n := n) (p := p) ((((n : ℕ) : ℝ) / (R : ℝ))) A qx) := by
  let shift : (Fin p →₀ ℕ) → (ParamIndex n p →₀ ℕ) := Finsupp.embDomain paramZEmb
  let a : ℝ := (((n : ℕ) : ℝ) / (R : ℝ))
  let outer := scalarOuterFactor (n := n) (p := p) M R
  let scaled := scaledMajorantPower (n := n) (p := p) a A qx
  let E' := E.filter fun ez ↦ shift ez ≤ d
  let pairFn : (Fin p →₀ ℕ) → (ParamIndex n p →₀ ℕ) × (ParamIndex n p →₀ ℕ) :=
    fun ez ↦ (shift ez, d - shift ez)
  have hrewrite :
      Finset.sum E (fun ez ↦
        if shift ez ≤ d then
          (M : ℝ) * (R : ℝ)⁻¹ ^ (qx + ∑ k : Fin p, ez k) *
            (((MvPowerSeries.coeff (d - shift ez) (A ^ qx) : NNReal) : ℝ))
        else
          0) =
        Finset.sum E' (fun ez ↦
          (M : ℝ) * (R : ℝ)⁻¹ ^ (qx + ∑ k : Fin p, ez k) *
            (((MvPowerSeries.coeff (d - shift ez) (A ^ qx) : NNReal) : ℝ))) := by
    simpa [E', shift] using
      (Finset.sum_filter (s := E) (p := fun ez ↦ shift ez ≤ d)
        (f := fun ez ↦
          (M : ℝ) * (R : ℝ)⁻¹ ^ (qx + ∑ k : Fin p, ez k) *
            (((MvPowerSeries.coeff (d - shift ez) (A ^ qx) : NNReal) : ℝ)))).symm
  have hterm :
      ∀ ez ∈ E',
        (M : ℝ) * (R : ℝ)⁻¹ ^ (qx + ∑ k : Fin p, ez k) *
            (((MvPowerSeries.coeff (d - shift ez) (A ^ qx) : NNReal) : ℝ)) ≤
          MvPowerSeries.coeff (shift ez) outer *
            MvPowerSeries.coeff (d - shift ez) scaled := by
    intro ez hez
    exact pureZWeightMul_shiftedCoeff_le_antidiagonalTerm
      (n := n) (p := p) M R qx ez d hn
  have hpair_inj : pairFn.Injective := by
    intro ez₁ ez₂ hEq
    have hfst := congrArg Prod.fst hEq
    have hcomap := congrArg
      (fun m : ParamIndex n p →₀ ℕ =>
        Finsupp.comapDomain (paramZEmb (n := n) (p := p)) m
          (paramZEmb (n := n) (p := p)).injective.injOn)
      hfst
    have hleft :
        Finsupp.comapDomain (paramZEmb (n := n) (p := p)) (shift ez₁)
          (paramZEmb (n := n) (p := p)).injective.injOn = ez₁ := by
      simp [shift]
    have hright :
        Finsupp.comapDomain (paramZEmb (n := n) (p := p)) (shift ez₂)
          (paramZEmb (n := n) (p := p)).injective.injOn = ez₂ := by
      simp [shift]
    exact hleft.symm.trans (hcomap.trans hright)
  have hsubset : E'.image pairFn ⊆ Finset.antidiagonal d := by
    intro e he
    rcases Finset.mem_image.mp he with ⟨ez, hez, rfl⟩
    exact Finset.mem_antidiagonal.mpr (add_tsub_cancel_of_le (Finset.mem_filter.mp hez).2)
  have himage_le :
      Finset.sum (E'.image pairFn) (fun e ↦
          MvPowerSeries.coeff e.1 outer * MvPowerSeries.coeff e.2 scaled) ≤
        Finset.sum (Finset.antidiagonal d) (fun e ↦
          MvPowerSeries.coeff e.1 outer * MvPowerSeries.coeff e.2 scaled) := by
    refine Finset.sum_le_sum_of_subset_of_nonneg hsubset ?_
    intro e he hnot
    exact mul_nonneg
      (outerCoeff_nonneg (n := n) (p := p) M R e.1)
      (coeffScaledMajorantPow_nonneg (n := n) (p := p) a (by positivity) A qx e.2)
  calc
    Finset.sum E (fun ez ↦
        if shift ez ≤ d then
          (M : ℝ) * (R : ℝ)⁻¹ ^ (qx + ∑ k : Fin p, ez k) *
            (((MvPowerSeries.coeff (d - shift ez) (A ^ qx) : NNReal) : ℝ))
        else
          0) =
      Finset.sum E' (fun ez ↦
        (M : ℝ) * (R : ℝ)⁻¹ ^ (qx + ∑ k : Fin p, ez k) *
          (((MvPowerSeries.coeff (d - shift ez) (A ^ qx) : NNReal) : ℝ))) :=
      hrewrite
    _ ≤ Finset.sum E' (fun ez ↦
          MvPowerSeries.coeff (shift ez) outer *
            MvPowerSeries.coeff (d - shift ez) scaled) := by
          exact Finset.sum_le_sum hterm
    _ = Finset.sum (E'.image pairFn) (fun e ↦
          MvPowerSeries.coeff e.1 outer * MvPowerSeries.coeff e.2 scaled) := by
          rw [Finset.sum_image hpair_inj.injOn]
    _ ≤ Finset.sum (Finset.antidiagonal d) (fun e ↦
          MvPowerSeries.coeff e.1 outer * MvPowerSeries.coeff e.2 scaled) :=
      himage_le
    _ = MvPowerSeries.coeff d (outer * scaled) := by
          rw [MvPowerSeries.coeff_mul]

/-- Helper for Cartan section29 0004_Exercise_2: after partitioning a fixed `x`-degree slice by
its pure-`z` part, the nonlinear source contribution is bounded by the corresponding owner-side
scalar coefficient. -/
lemma higherSubstSlice_le_outerMulScaledMajorantPowCoeff
    (S : RecursiveImplicitSystem 𝕜 n p)
    (M R : NNReal) (hS : S.IsMajorizedBy M R)
    {φ : Fin n → MvPowerSeries (ParamIndex n p) 𝕜}
    {A : MvPowerSeries (ParamIndex n p) NNReal}
    (hφ0 : ∀ j, MvPowerSeries.constantCoeff (φ j) = 0)
    (j : Fin n) (d : ParamIndex n p →₀ ℕ)
    (hA : ∀ j' e, paramDegree e < paramDegree d →
      ‖MvPowerSeries.coeff e (φ j')‖ ≤ (((MvPowerSeries.coeff e A : NNReal) : ℝ)))
    (qx : ℕ)
    (t : Finset ((Fin n ⊕ Fin p) →₀ ℕ))
    (hqx : 2 ≤ qx)
    (ht : ∀ m ∈ t, xDegree m = qx)
    (hn : 1 ≤ n) :
    Finset.sum t (fun m ↦
      ‖MvPowerSeries.coeff m (S.higher j) *
          MvPowerSeries.coeff d
            (m.prod fun s q ↦ (solutionSubst φ (higherToSystem s)) ^ q)‖) ≤
      MvPowerSeries.coeff d
        (scalarOuterFactor (n := n) (p := p) M R *
          scaledMajorantPower (n := n) (p := p) ((((n : ℕ) : ℝ) / (R : ℝ))) A qx) := by
  let zPart : ((Fin n ⊕ Fin p) →₀ ℕ) → (Fin p →₀ ℕ) :=
    fun m ↦ Finsupp.comapDomain Sum.inr m Sum.inr_injective.injOn
  let E : Finset (Fin p →₀ ℕ) := t.image zPart
  have hpartition :
      Finset.sum E (fun ez ↦
        Finset.sum (t.filter fun m ↦ zPart m = ez) (fun m ↦
          ‖MvPowerSeries.coeff m (S.higher j) *
              MvPowerSeries.coeff d
                (m.prod fun s q ↦ (solutionSubst φ (higherToSystem s)) ^ q)‖)) =
        Finset.sum t (fun m ↦
          ‖MvPowerSeries.coeff m (S.higher j) *
              MvPowerSeries.coeff d
                (m.prod fun s q ↦ (solutionSubst φ (higherToSystem s)) ^ q)‖) := by
    exact Finset.sum_fiberwise_of_maps_to
      (s := t) (t := E) (g := zPart)
      (fun m hm ↦ Finset.mem_image_of_mem zPart hm)
      (fun m ↦
        ‖MvPowerSeries.coeff m (S.higher j) *
            MvPowerSeries.coeff d
              (m.prod fun s q ↦ (solutionSubst φ (higherToSystem s)) ^ q)‖)
  have hfiber :
      ∀ ez ∈ E,
        Finset.sum (t.filter fun m ↦ zPart m = ez) (fun m ↦
          ‖MvPowerSeries.coeff m (S.higher j) *
              MvPowerSeries.coeff d
                (m.prod fun s q ↦ (solutionSubst φ (higherToSystem s)) ^ q)‖) ≤
          if Finsupp.embDomain paramZEmb ez ≤ d then
            (M : ℝ) * (R : ℝ)⁻¹ ^ (qx + ∑ k : Fin p, ez k) *
              (((MvPowerSeries.coeff
                  (d - Finsupp.embDomain paramZEmb ez) (A ^ qx) : NNReal) : ℝ))
          else
            0 := by
    intro ez hez
    exact higherSubstFiber_le_weightedShiftedCoeff
      (n := n) (p := p) S M R hS hφ0 j d hA qx ez
      (t.filter fun m ↦ zPart m = ez) hqx
      (fun m hm ↦
        ⟨ht m (Finset.mem_filter.mp hm).1, (Finset.mem_filter.mp hm).2⟩)
  calc
    Finset.sum t (fun m ↦
        ‖MvPowerSeries.coeff m (S.higher j) *
            MvPowerSeries.coeff d
              (m.prod fun s q ↦ (solutionSubst φ (higherToSystem s)) ^ q)‖) =
      Finset.sum E (fun ez ↦
        Finset.sum (t.filter fun m ↦ zPart m = ez) (fun m ↦
          ‖MvPowerSeries.coeff m (S.higher j) *
              MvPowerSeries.coeff d
                (m.prod fun s q ↦ (solutionSubst φ (higherToSystem s)) ^ q)‖)) := by
          symm
          exact hpartition
    _ ≤ Finset.sum E (fun ez ↦
          if Finsupp.embDomain paramZEmb ez ≤ d then
            (M : ℝ) * (R : ℝ)⁻¹ ^ (qx + ∑ k : Fin p, ez k) *
              (((MvPowerSeries.coeff
                  (d - Finsupp.embDomain paramZEmb ez) (A ^ qx) : NNReal) : ℝ))
          else
            0) := by
          exact Finset.sum_le_sum hfiber
    _ ≤ MvPowerSeries.coeff d
          (scalarOuterFactor (n := n) (p := p) M R *
            scaledMajorantPower (n := n) (p := p) ((((n : ℕ) : ℝ) / (R : ℝ))) A qx) := by
          exact weightedShiftedCoeffSum_le_outerMulScaledMajorantPowCoeff
            (n := n) (p := p) M R qx E d hn

end ScalarQuadraticMajorantExistence
