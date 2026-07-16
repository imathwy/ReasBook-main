import DifferentialForms_Cartan_1970.cartan.VII.section29.«0004_Exercise_2».OuterGeometricMajorant

open scoped BigOperators MvPowerSeries PowerSeries MvPowerSeries.WithPiTopology
open PowerSeries

universe u

section ScalarQuadraticMajorantExistence

variable {𝕜 : Type u} [NormedCommRing 𝕜]
variable {n p : ℕ}

/-- Helper for Cartan section29 0004_Exercise_2: coefficientwise majorant bounds are preserved
when multiplying two series, provided the bounds are known up to the target total degree. -/
lemma coeff_mul_norm_le_of_coeffLeWithin
    {φ ψ : MvPowerSeries (ParamIndex n p) 𝕜}
    {A B : MvPowerSeries (ParamIndex n p) NNReal}
    (d : ParamIndex n p →₀ ℕ)
    (hA : ∀ e, paramDegree e ≤ paramDegree d →
      ‖MvPowerSeries.coeff e φ‖ ≤ (((MvPowerSeries.coeff e A : NNReal) : ℝ)))
    (hB : ∀ e, paramDegree e ≤ paramDegree d →
      ‖MvPowerSeries.coeff e ψ‖ ≤ (((MvPowerSeries.coeff e B : NNReal) : ℝ))) :
    ‖MvPowerSeries.coeff d (φ * ψ)‖ ≤
      (((MvPowerSeries.coeff d (A * B) : NNReal) : ℝ)) := by
  calc
    ‖MvPowerSeries.coeff d (φ * ψ)‖ ≤
        Finset.sum (Finset.antidiagonal d)
          (fun e ↦ ‖MvPowerSeries.coeff e.1 φ * MvPowerSeries.coeff e.2 ψ‖) := by
            simpa [MvPowerSeries.coeff_mul] using
              (norm_sum_le (s := Finset.antidiagonal d)
                (f := fun e ↦
                  MvPowerSeries.coeff e.1 φ * MvPowerSeries.coeff e.2 ψ))
    _ ≤ Finset.sum (Finset.antidiagonal d)
          (fun e ↦
            (((MvPowerSeries.coeff e.1 A : NNReal) : ℝ) *
              (((MvPowerSeries.coeff e.2 B : NNReal) : ℝ)))) := by
            refine Finset.sum_le_sum ?_
            intro e he
            have hsum : e.1 + e.2 = d := Finset.mem_antidiagonal.mp he
            have hdeg :
                paramDegree e.1 + paramDegree e.2 = paramDegree d := by
              rw [← hsum]
              simp [paramDegree, Finset.sum_add_distrib]
            have hle1 : paramDegree e.1 ≤ paramDegree d := by
              omega
            have hle2 : paramDegree e.2 ≤ paramDegree d := by
              omega
            exact le_trans (norm_mul_le _ _)
              (mul_le_mul (hA e.1 hle1) (hB e.2 hle2) (by positivity) (by positivity))
    _ = (((MvPowerSeries.coeff d (A * B) : NNReal) : ℝ)) := by
      rw [MvPowerSeries.coeff_mul]
      norm_num

/-- Helper for Cartan section29 0004_Exercise_2: once every coefficient of `φ` below total degree
`N` is dominated by the corresponding coefficient of `A`, the same remains true for every
positive power of `φ` at target degrees still below `N`. -/
lemma coeff_pow_norm_le_ofCoeffLeBelow
    {φ : MvPowerSeries (ParamIndex n p) 𝕜}
    {A : MvPowerSeries (ParamIndex n p) NNReal}
    {N : ℕ}
    (hA : ∀ e, paramDegree e < N →
      ‖MvPowerSeries.coeff e φ‖ ≤ (((MvPowerSeries.coeff e A : NNReal) : ℝ))) :
    ∀ q d, paramDegree d < N →
      ‖MvPowerSeries.coeff d (φ ^ (q + 1))‖ ≤
        (((MvPowerSeries.coeff d (A ^ (q + 1)) : NNReal) : ℝ))
  | 0, d, hd => by
      -- The first power is the original series itself.
      simpa using hA d hd
  | q + 1, d, hd => by
      -- Compare the next positive power by viewing it as the product of the previous one and one
      -- more copy of `φ`.
      simpa [pow_succ, Nat.add_assoc] using
        coeff_mul_norm_le_of_coeffLeWithin (n := n) (p := p)
          (φ := φ ^ (q + 1)) (ψ := φ) (A := A ^ (q + 1)) (B := A) d
          (fun e he ↦
            coeff_pow_norm_le_ofCoeffLeBelow hA q e (lt_of_le_of_lt he hd))
          (fun e he ↦ hA e (lt_of_le_of_lt he hd))

/-- Helper for Cartan section29 0004_Exercise_2: if `φ` has zero constant coefficient and the
coefficients below total degree `N` are bounded by `A`, then the degree-`N` coefficient of every
power `φ^q` with `q ≥ 2` is bounded by the corresponding coefficient of `A^q`. -/
lemma coeffPowNorm_le_ofCoeffLeBelow_of_two_le
    {φ : MvPowerSeries (ParamIndex n p) 𝕜}
    {A : MvPowerSeries (ParamIndex n p) NNReal}
    {N q : ℕ}
    (hq : 2 ≤ q)
    (hφ0 : MvPowerSeries.constantCoeff φ = 0)
    (hA : ∀ e, paramDegree e < N →
      ‖MvPowerSeries.coeff e φ‖ ≤ (((MvPowerSeries.coeff e A : NNReal) : ℝ)))
    (d : ParamIndex n p →₀ ℕ)
    (hd : paramDegree d = N) :
    ‖MvPowerSeries.coeff d (φ ^ q)‖ ≤
      (((MvPowerSeries.coeff d (A ^ q) : NNReal) : ℝ)) := by
  classical
  have hqne : (Finset.range q).Nonempty := by
    refine Finset.nonempty_range_iff.mpr ?_
    omega
  calc
    ‖MvPowerSeries.coeff d (φ ^ q)‖ ≤
        Finset.sum (Finset.finsuppAntidiag (Finset.range q) d)
          (fun l ↦ ‖∏ i ∈ Finset.range q, MvPowerSeries.coeff (l i) φ‖) := by
            simpa [MvPowerSeries.coeff_pow] using
              (norm_sum_le (s := Finset.finsuppAntidiag (Finset.range q) d)
                (f := fun l ↦ ∏ i ∈ Finset.range q, MvPowerSeries.coeff (l i) φ))
    _ ≤ Finset.sum (Finset.finsuppAntidiag (Finset.range q) d)
          (fun l ↦ ∏ i ∈ Finset.range q,
            (((MvPowerSeries.coeff (l i) A : NNReal) : ℝ))) := by
            refine Finset.sum_le_sum ?_
            intro l hl
            have hl' := Finset.mem_finsuppAntidiag.mp hl
            have hsumdeg : N = ∑ i ∈ Finset.range q, paramDegree (l i) := by
              rw [← hd, paramDegree_eq_degree, ← hl'.1]
              simp [paramDegree_eq_degree, map_sum]
            by_cases hlt : ∀ i ∈ Finset.range q, paramDegree (l i) < N
            · -- If every factor stays below total degree `N`, compare every factor coefficient
              -- directly and then multiply the bounds.
              calc
                ‖∏ i ∈ Finset.range q, MvPowerSeries.coeff (l i) φ‖ ≤
                    ∏ i ∈ Finset.range q, ‖MvPowerSeries.coeff (l i) φ‖ := by
                      exact Finset.norm_prod_le' (Finset.range q) hqne
                        (fun i ↦ MvPowerSeries.coeff (l i) φ)
                _ ≤ ∏ i ∈ Finset.range q,
                      (((MvPowerSeries.coeff (l i) A : NNReal) : ℝ)) := by
                        exact Finset.prod_le_prod
                          (fun i hi ↦ norm_nonneg _)
                          (fun i hi ↦ hA (l i) (hlt i hi))
            · -- Otherwise one factor already has total degree `N`; because `q ≥ 2`, another
              -- factor is forced into degree `0`, so the whole product vanishes on the source
              -- side while the scalar-side product stays nonnegative.
              push Not at hlt
              rcases hlt with ⟨i, hi, hNi⟩
              have hli_le : paramDegree (l i) ≤ N := by
                rw [hsumdeg]
                simpa using
                  (Finset.single_le_sum
                    (fun j hj ↦ Nat.zero_le (paramDegree (l j))) hi :
                      paramDegree (l i) ≤ ∑ j ∈ Finset.range q, paramDegree (l j))
              have hli_eq : paramDegree (l i) = N := le_antisymm hli_le hNi
              have hsumErase : ∑ j ∈ (Finset.range q).erase i, paramDegree (l j) = 0 := by
                have hsplit :
                    ∑ j ∈ Finset.range q, paramDegree (l j) =
                      paramDegree (l i) + ∑ j ∈ (Finset.range q).erase i, paramDegree (l j) := by
                  simpa [Finset.sdiff_singleton_eq_erase] using
                    (Finset.sum_eq_add_sum_diff_singleton_of_mem
                      (f := fun j ↦ paramDegree (l j)) hi :
                        ∑ j ∈ Finset.range q, paramDegree (l j) =
                          paramDegree (l i) + ∑ x ∈ Finset.range q \ {i},
                            paramDegree (l x))
                have hsumdeg' : ∑ j ∈ Finset.range q, paramDegree (l j) = N := hsumdeg.symm
                rw [hsumdeg', hli_eq] at hsplit
                have hsub := congrArg (fun t : ℕ => t - N) hsplit.symm
                simpa using hsub
              have hcardErasePos : 0 < ((Finset.range q).erase i).card := by
                rw [Finset.card_erase_of_mem hi, Finset.card_range]
                omega
              rcases Finset.card_pos.mp hcardErasePos with ⟨j, hj⟩
              have hjrange : j ∈ Finset.range q := (Finset.mem_erase.mp hj).2
              have hjdeg0 : paramDegree (l j) = 0 := by
                have hle :
                    paramDegree (l j) ≤ ∑ k ∈ (Finset.range q).erase i, paramDegree (l k) := by
                  exact Finset.single_le_sum
                    (fun k hk ↦ Nat.zero_le (paramDegree (l k))) hj
                rw [hsumErase] at hle
                exact Nat.eq_zero_of_le_zero hle
              have hjEq0 : l j = 0 := (paramDegree_eq_zero_iff (n := n) (p := p) (l j)).mp hjdeg0
              have hcoeffφ0 : MvPowerSeries.coeff (l j) φ = 0 := by
                simpa [hjEq0, MvPowerSeries.coeff_zero_eq_constantCoeff_apply] using hφ0
              have hprodZero :
                  ∏ k ∈ Finset.range q, MvPowerSeries.coeff (l k) φ = 0 := by
                rw [← Finset.mul_prod_erase (s := Finset.range q)
                  (f := fun k ↦ MvPowerSeries.coeff (l k) φ) hjrange, hcoeffφ0, zero_mul]
              rw [hprodZero]
              have hnonneg :
                  0 ≤ ∏ i ∈ Finset.range q,
                    (((MvPowerSeries.coeff (l i) A : NNReal) : ℝ)) := by
                      exact Finset.prod_nonneg (fun i hi ↦ by positivity)
              simpa using hnonneg
    _ = (((MvPowerSeries.coeff d (A ^ q) : NNReal) : ℝ)) := by
      rw [MvPowerSeries.coeff_pow]
      norm_num

/-- Helper for Cartan section29 0004_Exercise_2: if every cutoff component is coefficientwise
dominated by `A` below total degree `N`, then the same domination holds for the coefficient of
every pure `x`-monomial with total `x`-degree at least `2` at target degrees up to `N`. -/
lemma coeffFinsuppProdXpowers_norm_le_ofCoeffLe
    {φ : Fin n → MvPowerSeries (ParamIndex n p) 𝕜}
    {A : MvPowerSeries (ParamIndex n p) NNReal}
    {N : ℕ}
    (hφ0 : ∀ j, MvPowerSeries.constantCoeff (φ j) = 0)
    (hA : ∀ j e, paramDegree e < N →
      ‖MvPowerSeries.coeff e (φ j)‖ ≤ (((MvPowerSeries.coeff e A : NNReal) : ℝ)))
    (m : Fin n →₀ ℕ)
    (hm : 2 ≤ m.sum fun _ q ↦ q)
    (d : ParamIndex n p →₀ ℕ)
    (hd : paramDegree d ≤ N) :
    ‖MvPowerSeries.coeff d (m.prod fun j q ↦ (φ j) ^ q)‖ ≤
      (((MvPowerSeries.coeff d (A ^ (m.sum fun _ q ↦ q)) : NNReal) : ℝ)) := by
  classical
  have hprodA : m.prod (fun j q ↦ A ^ q) = A ^ (m.sum fun _ q ↦ q) := by
    -- All factors on the scalar side are powers of the same series `A`.
    simpa [Finsupp.prod, Finsupp.sum] using
      (Finset.prod_pow_eq_pow_sum (s := m.support) (f := fun j ↦ m j) (a := A))
  have hsuppNonempty : m.support.Nonempty := by
    by_contra hsupp
    rw [Finset.not_nonempty_iff_eq_empty] at hsupp
    have hsum0 : m.sum (fun _ q ↦ q) = 0 := by
      simp [Finsupp.sum, hsupp]
    omega
  calc
    ‖MvPowerSeries.coeff d (m.prod fun j q ↦ (φ j) ^ q)‖ ≤
        Finset.sum (Finset.finsuppAntidiag m.support d)
          (fun l ↦ ‖∏ j ∈ m.support, MvPowerSeries.coeff (l j) ((φ j) ^ m j)‖) := by
            simpa [Finsupp.prod, MvPowerSeries.coeff_prod] using
              (norm_sum_le (s := Finset.finsuppAntidiag m.support d)
                (f := fun l ↦ ∏ j ∈ m.support, MvPowerSeries.coeff (l j) ((φ j) ^ m j)))
    _ ≤ Finset.sum (Finset.finsuppAntidiag m.support d)
          (fun l ↦ ∏ j ∈ m.support,
            (((MvPowerSeries.coeff (l j) (A ^ m j) : NNReal) : ℝ))) := by
            refine Finset.sum_le_sum ?_
            intro l hl
            have hl' := Finset.mem_finsuppAntidiag.mp hl
            have hsumdeg : paramDegree d = ∑ j ∈ m.support, paramDegree (l j) := by
              rw [paramDegree_eq_degree, ← hl'.1]
              simp [paramDegree_eq_degree, map_sum]
            by_cases hlt : ∀ j ∈ m.support, paramDegree (l j) < paramDegree d
            · -- When every factor degree is already below the target, compare each power
              -- coefficient directly and then multiply the bounds.
              calc
                ‖∏ j ∈ m.support, MvPowerSeries.coeff (l j) ((φ j) ^ m j)‖ ≤
                    ∏ j ∈ m.support, ‖MvPowerSeries.coeff (l j) ((φ j) ^ m j)‖ := by
                      exact Finset.norm_prod_le' m.support hsuppNonempty
                        (fun j ↦ MvPowerSeries.coeff (l j) ((φ j) ^ m j))
                _ ≤ ∏ j ∈ m.support,
                      (((MvPowerSeries.coeff (l j) (A ^ m j) : NNReal) : ℝ)) := by
                        exact Finset.prod_le_prod
                          (fun j hj ↦ norm_nonneg _)
                          (fun j hj ↦ by
                            have hmj : 0 < m j := Nat.pos_iff_ne_zero.mpr
                              (Finsupp.mem_support_iff.mp hj)
                            rcases Nat.exists_eq_succ_of_ne_zero hmj.ne' with ⟨qj, hqj⟩
                            rw [hqj]
                            exact coeff_pow_norm_le_ofCoeffLeBelow (n := n) (p := p)
                              (φ := φ j) (A := A) (N := N)
                              (fun e he ↦ hA j e he)
                              qj (l j) (lt_of_lt_of_le (hlt j hj) hd))
            · -- Otherwise one factor already has the full degree of `d`. If the support still has
              -- another positive exponent, the whole product vanishes because that extra factor is
              -- forced into degree `0`; otherwise we are in the singleton-support case and the
              -- exact-degree power lemma applies.
              push Not at hlt
              rcases hlt with ⟨i, hi, hige⟩
              have hil : paramDegree (l i) ≤ paramDegree d := by
                simpa [hsumdeg] using
                  (Finset.single_le_sum
                    (fun j hj ↦ Nat.zero_le (paramDegree (l j))) hi :
                      paramDegree (l i) ≤ ∑ j ∈ m.support, paramDegree (l j))
              have hieq : paramDegree (l i) = paramDegree d := le_antisymm hil hige
              by_cases hs : (m.support.erase i).Nonempty
              · rcases hs with ⟨k, hk⟩
                have hsplit :
                    ∑ j ∈ m.support, paramDegree (l j) =
                      paramDegree (l i) + ∑ j ∈ m.support.erase i, paramDegree (l j) := by
                  simpa [Finset.sdiff_singleton_eq_erase] using
                    (Finset.sum_eq_add_sum_diff_singleton_of_mem
                      (f := fun j ↦ paramDegree (l j)) hi :
                        ∑ j ∈ m.support, paramDegree (l j) =
                          paramDegree (l i) + ∑ x ∈ m.support \ {i},
                            paramDegree (l x))
                have hsumErase : ∑ j ∈ m.support.erase i, paramDegree (l j) = 0 := by
                  omega
                have hkdeg0 : paramDegree (l k) = 0 := by
                  have hle :
                      paramDegree (l k) ≤ ∑ j ∈ m.support.erase i, paramDegree (l j) := by
                    simpa using
                      (Finset.single_le_sum
                        (fun j hj ↦ Nat.zero_le (paramDegree (l j))) hk :
                          paramDegree (l k) ≤ ∑ j ∈ m.support.erase i, paramDegree (l j))
                  rw [hsumErase] at hle
                  exact Nat.eq_zero_of_le_zero hle
                have hkcoeffφ : MvPowerSeries.coeff (l k) ((φ k) ^ m k) = 0 := by
                  have hk0 : l k = 0 :=
                    (paramDegree_eq_zero_iff (n := n) (p := p) (l k)).mp hkdeg0
                  have hmk : 0 < m k := Nat.pos_iff_ne_zero.mpr
                    (Finsupp.mem_support_iff.mp ((Finset.mem_erase.mp hk).2))
                  simpa [hk0, hmk.ne'] using
                    (show MvPowerSeries.coeff 0 ((φ k) ^ m k) = 0 by
                      rw [MvPowerSeries.coeff_zero_eq_constantCoeff_apply]
                      simp [hφ0 k, hmk.ne'])
                have hprodZero :
                    ∏ j ∈ m.support, MvPowerSeries.coeff (l j) ((φ j) ^ m j) = 0 := by
                  rw [← Finset.mul_prod_erase (s := m.support)
                    (f := fun j ↦ MvPowerSeries.coeff (l j) ((φ j) ^ m j))
                    ((Finset.mem_erase.mp hk).2), hkcoeffφ, zero_mul]
                rw [hprodZero]
                have hnonneg :
                    0 ≤ ∏ j ∈ m.support,
                      (((MvPowerSeries.coeff (l j) (A ^ m j) : NNReal) : ℝ)) := by
                        exact Finset.prod_nonneg (fun j hj ↦ by positivity)
                simpa using hnonneg
              · have hsupp : m.support = {i} := by
                  apply Finset.eq_singleton_iff_nonempty_unique_mem.mpr
                  refine ⟨⟨i, hi⟩, ?_⟩
                  intro j hj
                  by_contra hji
                  exact hs ⟨j, by simpa [hji] using hj⟩
                have hmi : 2 ≤ m i := by
                  simpa [Finsupp.sum, hsupp] using hm
                -- In the singleton-support case the whole product is one power, so the exact-
                -- degree power majorant closes the comparison.
                simpa [hsupp] using
                  (coeffPowNorm_le_ofCoeffLeBelow_of_two_le (n := n) (p := p)
                  (φ := φ i) (A := A) (N := paramDegree d) (q := m i) hmi (hφ0 i)
                  (fun e he ↦ hA i e (lt_of_lt_of_le he hd)) (l i) hieq)
    _ = (((MvPowerSeries.coeff d (m.prod fun j q ↦ A ^ q) : NNReal) : ℝ)) := by
      rw [Finsupp.prod, MvPowerSeries.coeff_prod]
      norm_num
    _ = (((MvPowerSeries.coeff d (A ^ (m.sum fun _ q ↦ q)) : NNReal) : ℝ)) := by
      rw [hprodA]

/-- Helper for Cartan section29 0004_Exercise_2: after splitting a higher monomial into its pure
`x` and pure `z` parts, the substituted coefficient is controlled by the corresponding shifted
coefficient of the pure `x` majorant power. -/
lemma coeffSolutionSubstHigherMonomial_norm_le_ofCoeffLe
    {φ : Fin n → MvPowerSeries (ParamIndex n p) 𝕜}
    {A : MvPowerSeries (ParamIndex n p) NNReal}
    (hφ0 : ∀ j, MvPowerSeries.constantCoeff (φ j) = 0)
    (hA : ∀ j e, paramDegree e < paramDegree d →
      ‖MvPowerSeries.coeff e (φ j)‖ ≤ (((MvPowerSeries.coeff e A : NNReal) : ℝ)))
    (m : Fin n ⊕ Fin p →₀ ℕ)
    (hm : 2 ≤ xDegree m) :
    ‖MvPowerSeries.coeff d
        (m.prod fun s q ↦
          (solutionSubst φ (higherToSystem s)) ^ q)‖ ≤
      if Finsupp.embDomain paramZEmb
            (Finsupp.comapDomain Sum.inr m Sum.inr_injective.injOn) ≤ d then
        (((MvPowerSeries.coeff
            (d - Finsupp.embDomain paramZEmb
              (Finsupp.comapDomain Sum.inr m Sum.inr_injective.injOn))
            (A ^ xDegree m) : NNReal) : ℝ))
      else
        0 := by
  classical
  let mx : Fin n →₀ ℕ :=
    Finsupp.comapDomain Sum.inl m Sum.inl_injective.injOn
  let mz : Fin p →₀ ℕ :=
    Finsupp.comapDomain Sum.inr m Sum.inr_injective.injOn
  have hmdecomp : mx.sumElim mz = m := by
    simp [mx, mz]
  have hmxsum : mx.sum (fun _ q ↦ q) = xDegree m := by
    rw [Finsupp.sum]
    refine Finset.sum_subset (by simp) ?_
    intro j _ hj
    have hj' : Sum.inl j ∉ m.support := by
      simpa using hj
    simpa [mx, xDegree, Finsupp.mem_support_iff] using hj'
  have hmx : 2 ≤ mx.sum fun _ q ↦ q := by
    rw [hmxsum]
    exact hm
  have hsplit :
      (m.prod fun s q ↦ (solutionSubst φ (higherToSystem s)) ^ q) =
        mx.prod (fun j q ↦ (φ j) ^ q) *
          MvPowerSeries.monomial
            (Finsupp.embDomain paramZEmb mz) (1 : 𝕜) := by
    -- Split the substituted higher monomial into its pure `x` product and its pure `z` monomial.
    rw [← hmdecomp, Finsupp.prod_sumElim]
    rw [Finsupp.prod, Finsupp.prod]
    refine congrArg₂ (· * ·) ?_ ?_
    · refine Finset.prod_subset (by simp) ?_
      intro j _ hj
      have hmj0 : mx j = 0 := by
        simpa [Finsupp.mem_support_iff] using hj
      simp [solutionSubst, higherToSystem, hmj0]
    · calc
        mz.prod (fun k q ↦ (solutionSubst φ (higherToSystem (Sum.inr k))) ^ q) =
            ∏ k ∈ mz.support,
              (MvPowerSeries.X (Sum.inr k) : MvPowerSeries (ParamIndex n p) 𝕜) ^ mz k := by
                refine Finset.prod_subset (by simp) ?_
                intro k _ hk
                have hmk0 : mz k = 0 := by
                  simpa [Finsupp.mem_support_iff] using hk
                simp [solutionSubst, higherToSystem, zToSystem, hmk0]
        _ = MvPowerSeries.monomial
              (Finsupp.embDomain paramZEmb mz) (1 : 𝕜) := by
              simpa using pureZProduct_eq_monomial (𝕜 := 𝕜) (n := n) (p := p) mz
  rw [hsplit]
  by_cases hshift :
      Finsupp.embDomain paramZEmb
          (Finsupp.comapDomain Sum.inr m Sum.inr_injective.injOn) ≤ d
  · have hcoeff :
        MvPowerSeries.coeff d
          (mx.prod (fun j q ↦ (φ j) ^ q) *
            MvPowerSeries.monomial
              (Finsupp.embDomain paramZEmb mz) (1 : 𝕜)) =
          MvPowerSeries.coeff
            (d - Finsupp.embDomain paramZEmb mz)
            (mx.prod fun j q ↦ (φ j) ^ q) := by
      simpa [mx, mz, hshift] using
        (MvPowerSeries.coeff_mul_monomial
          (m := d)
          (n := Finsupp.embDomain paramZEmb mz)
          (φ := mx.prod fun j q ↦ (φ j) ^ q)
          (a := (1 : 𝕜)))
    rw [hcoeff, if_pos hshift]
    have hdeg :
        paramDegree (d - Finsupp.embDomain paramZEmb mz) ≤ paramDegree d := by
      have hsum :
          (d - Finsupp.embDomain paramZEmb mz) +
              Finsupp.embDomain paramZEmb mz = d := by
        exact tsub_add_cancel_of_le hshift
      have hparam :
          paramDegree (n := n) (p := p) (d - Finsupp.embDomain paramZEmb mz) +
              paramDegree (n := n) (p := p) (Finsupp.embDomain paramZEmb mz) =
            paramDegree (n := n) (p := p) d := by
        rw [← hsum, paramDegree, paramDegree, paramDegree]
        simp [Finset.sum_add_distrib]
      omega
    -- Once the pure `z` monomial has been peeled off, the existing pure `x` product majorant
    -- applies to the shifted coefficient.
    simpa [mx, mz, hmxsum] using
      (coeffFinsuppProdXpowers_norm_le_ofCoeffLe (n := n) (p := p)
        (φ := φ) (A := A) hφ0 hA mx (by simpa [hmxsum] using hmx)
        (d - Finsupp.embDomain paramZEmb mz) hdeg)
  · have hcoeff :
        MvPowerSeries.coeff d
          (mx.prod (fun j q ↦ (φ j) ^ q) *
            MvPowerSeries.monomial
              (Finsupp.embDomain paramZEmb mz) (1 : 𝕜)) = 0 := by
      simpa [mx, mz, hshift] using
        (MvPowerSeries.coeff_mul_monomial
          (m := d)
          (n := Finsupp.embDomain paramZEmb mz)
          (φ := mx.prod fun j q ↦ (φ j) ^ q)
          (a := (1 : 𝕜)))
    rw [hcoeff]
    simp [hshift]

end ScalarQuadraticMajorantExistence
