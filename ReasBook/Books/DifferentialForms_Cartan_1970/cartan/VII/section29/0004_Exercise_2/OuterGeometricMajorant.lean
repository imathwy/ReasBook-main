import DifferentialForms_Cartan_1970.VII.section29.«0004_Exercise_2».ScalarQuadraticMajorant

open scoped BigOperators MvPowerSeries PowerSeries MvPowerSeries.WithPiTopology
open PowerSeries

universe u

section ScalarQuadraticMajorantExistence

variable {𝕜 : Type u} [NormedCommRing 𝕜]
variable {n p : ℕ}

def paramZEmb : Fin p ↪ ParamIndex n p :=
  ⟨Sum.inr, Sum.inr_injective⟩

/-- Helper for Cartan section29 0004_Exercise_2: the pure `z` variables occurring in a higher
monomial multiply to the single corresponding `z`-monomial in the `(y, z)` parameter ring. -/
lemma pureZProduct_eq_monomial
    (mz : Fin p →₀ ℕ) :
    ∏ k ∈ mz.support,
        ((MvPowerSeries.X (Sum.inr k) : MvPowerSeries (ParamIndex n p) 𝕜) ^ mz k) =
      (MvPowerSeries.monomial
        (Finsupp.embDomain paramZEmb mz) (1 : 𝕜) :
          MvPowerSeries (ParamIndex n p) 𝕜) := by
  classical
  refine Finsupp.induction mz ?_ ?_
  · -- The empty pure-`z` monomial contributes the multiplicative identity.
    simp
  · intro a b f ha hb ih
    have hfa : f a = 0 := by
      simpa [Finsupp.mem_support_iff] using ha
    have hsupp : ((Finsupp.single a b : Fin p →₀ ℕ) + f).support = insert a f.support := by
      rw [Finsupp.support_add_eq]
      · rw [Finsupp.support_single a hb]
        simp
      · rw [Finsupp.support_single a hb]
        exact Finset.disjoint_singleton_left.mpr ha
    have htail :
        ∏ x ∈ f.support,
          ((MvPowerSeries.X (Sum.inr x) : MvPowerSeries (ParamIndex n p) 𝕜) ^
            (((Finsupp.single a b : Fin p →₀ ℕ) + f) x)) =
          ∏ x ∈ f.support,
            ((MvPowerSeries.X (Sum.inr x) : MvPowerSeries (ParamIndex n p) 𝕜) ^ f x) := by
      -- Away from the newly inserted variable, the exponents are unchanged.
      refine Finset.prod_congr rfl ?_
      intro x hx
      have hxa : x ≠ a := by
        intro hxa
        subst hxa
        exact ha hx
      simp [Finsupp.add_apply, hxa]
    have hEmb :
        ((Finsupp.single (Sum.inr a) b : ParamIndex n p →₀ ℕ) +
            Finsupp.embDomain (paramZEmb (n := n) (p := p)) f : ParamIndex n p →₀ ℕ) =
          (Finsupp.embDomain (paramZEmb (n := n) (p := p))
            ((Finsupp.single a b : Fin p →₀ ℕ) + f) : ParamIndex n p →₀ ℕ) := by
      -- Embedding the pure `z` exponents commutes with adjoining the new singleton exponent.
      ext s
      cases s with
      | inl i => simp [paramZEmb, Finsupp.add_apply]
      | inr j =>
          by_cases h : j = a
          · subst h
            simp [paramZEmb, Finsupp.embDomain_single, Finsupp.add_apply]
          · simp [paramZEmb, Finsupp.embDomain_single, Finsupp.add_apply, h]
    rw [hsupp, Finset.prod_insert ha, htail]
    -- Collapse the new singleton factor to a monomial and multiply it with the induction target.
    simp only [Finsupp.coe_add, Pi.add_apply, Finsupp.single_eq_same, Finsupp.embDomain_add,
      Finsupp.embDomain_single]
    rw [hfa, add_zero]
    rw [show ((MvPowerSeries.X (Sum.inr a) : MvPowerSeries (ParamIndex n p) 𝕜) ^ b) =
        MvPowerSeries.monomial (Finsupp.single (Sum.inr a) b) (1 : 𝕜) by
          simpa using
            (MvPowerSeries.X_pow_eq (R := 𝕜) (σ := ParamIndex n p) (s := Sum.inr a) (n := b)),
      ih, MvPowerSeries.monomial_mul_monomial, hEmb]
    simp

/-- Helper for Cartan section29 0004_Exercise_2: multiplying a geometric `z`-kernel by its owner
series gives the predecessor-coefficient recursion used to bound the pure `z` coefficients of the
outer majorant factor from below. -/
lemma coeff_scaledParamZMul_eq_sum
    (b : ℝ) (G : MvPowerSeries (Fin p) ℝ) (e : Fin p →₀ ℕ) :
    MvPowerSeries.coeff e ((MvPowerSeries.C b) * (∑ k : Fin p, MvPowerSeries.X k) * G) =
      b * ∑ k : Fin p,
        if Finsupp.single k 1 ≤ e then
          MvPowerSeries.coeff (e - Finsupp.single k 1) G
        else
          0 := by
  classical
  by_cases hb : b = 0
  · subst hb
    simp
  rw [mul_assoc, MvPowerSeries.coeff_C_mul, Finset.sum_mul]
  have hcoeffSum :
      MvPowerSeries.coeff e (∑ k : Fin p, MvPowerSeries.X k * G) =
        ∑ k : Fin p, MvPowerSeries.coeff e (MvPowerSeries.X k * G) := by
    simp
  rw [hcoeffSum]
  simp_rw [MvPowerSeries.X, MvPowerSeries.coeff_monomial_mul]
  simp

/-- Helper for Cartan section29 0004_Exercise_2: the inverse of `1 - b (Z₁ + ⋯ + Zₚ)` satisfies
the expected predecessor-coefficient recursion on every nonzero pure `z` exponent. -/
lemma coeff_geometricParamZInv_eq_sumPred
    (b : NNReal) (e : Fin p →₀ ℕ) (he : e ≠ 0) :
    MvPowerSeries.coeff e ((1 - MvPowerSeries.C (b : ℝ) * (∑ k : Fin p, MvPowerSeries.X k))⁻¹) =
      (b : ℝ) * ∑ k : Fin p,
        if Finsupp.single k 1 ≤ e then
          MvPowerSeries.coeff (e - Finsupp.single k 1)
            ((1 - MvPowerSeries.C (b : ℝ) * (∑ i : Fin p, MvPowerSeries.X i))⁻¹)
        else
          0 := by
  let A : MvPowerSeries (Fin p) ℝ :=
    MvPowerSeries.C (b : ℝ) * (∑ i : Fin p, MvPowerSeries.X i)
  let G : MvPowerSeries (Fin p) ℝ :=
    ((1 - MvPowerSeries.C (b : ℝ) * (∑ i : Fin p, MvPowerSeries.X i))⁻¹)
  have hEqOne :
      (1 - A) * G = 1 := by
    simp [A, G]
  have h := congrArg (MvPowerSeries.coeff e) hEqOne
  have hpred :
      MvPowerSeries.coeff e G = MvPowerSeries.coeff e (A * G) := by
    have hzero : MvPowerSeries.coeff e (1 : MvPowerSeries (Fin p) ℝ) = 0 := by
      simp [MvPowerSeries.coeff_one, he]
    apply sub_eq_zero.mp
    rw [hzero] at h
    simpa [A, sub_eq_add_neg, add_mul] using h
  simpa [A, G, coeff_scaledParamZMul_eq_sum] using hpred

/-- Helper for Cartan section29 0004_Exercise_2: every pure `z` coefficient of the geometric
factor `(1 - b (Z₁ + ⋯ + Zₚ))⁻¹` dominates the simple scalar weight `b^q` at total degree `q`. -/
lemma geometricParamZInv_coeff_lower
    (b : NNReal) :
    ∀ (q : ℕ) (e : Fin p →₀ ℕ), (∑ k : Fin p, e k) = q →
      (b : ℝ) ^ q ≤
        MvPowerSeries.coeff e
          ((1 - MvPowerSeries.C (b : ℝ) * (∑ k : Fin p, MvPowerSeries.X k))⁻¹)
  | 0, e, heq => by
      have he0 : e = 0 := by
        apply Finsupp.ext
        intro k
        have hk : e k ≤ ∑ i : Fin p, e i := by
          exact Finset.single_le_sum (fun _ _ ↦ Nat.zero_le _) (by simp)
        rw [heq] at hk
        exact Nat.eq_zero_of_le_zero hk
      subst he0
      simp
  | q + 1, e, heq => by
      have he : e ≠ 0 := by
        intro h
        subst h
        simp at heq
      have hsupp : e.support.Nonempty := by
        simpa [Finsupp.support_eq_empty] using he
      rcases hsupp with ⟨k, hk⟩
      let ek : Fin p →₀ ℕ := Finsupp.single k 1
      have hkpos : 0 < e k := Nat.pos_iff_ne_zero.mpr (Finsupp.mem_support_iff.mp hk)
      have hk_le : ek ≤ e := by
        intro t
        by_cases ht : t = k
        · subst ht
          simpa [ek] using Nat.succ_le_of_lt hkpos
        · simp [ek, Finsupp.single_eq_of_ne ht]
      have hsum_sub : (∑ i : Fin p, (e - ek) i) = q := by
        have htsub :
            ∑ i : Fin p, (e - ek) i = (∑ i : Fin p, e i) - ∑ i : Fin p, ek i := by
          simpa using
            (Finset.sum_tsub_distrib Finset.univ (by
              intro i hi
              exact hk_le i))
        rw [htsub]
        simp [ek, heq]
      have hrec := geometricParamZInv_coeff_lower b q (e - ek) hsum_sub
      have hnonneg :
          ∀ i : Fin p,
            0 ≤
              if Finsupp.single i 1 ≤ e then
                MvPowerSeries.coeff (e - Finsupp.single i 1)
                  ((1 - MvPowerSeries.C (b : ℝ) * (∑ j : Fin p, MvPowerSeries.X j))⁻¹)
              else
                0 := by
        intro i
        by_cases hi : Finsupp.single i 1 ≤ e
        · let ei : Fin p →₀ ℕ := Finsupp.single i 1
          have hsum_i : (∑ t : Fin p, (e - ei) t) = q := by
            have htsub :
                ∑ t : Fin p, (e - ei) t = (∑ t : Fin p, e t) - ∑ t : Fin p, ei t := by
              simpa using
                (Finset.sum_tsub_distrib Finset.univ (by
                  intro t ht
                  exact hi t))
            rw [htsub, show ∑ t : Fin p, ei t = 1 by simp [ei]]
            simp [heq]
          have hcoeff_nonneg :
              0 ≤
                MvPowerSeries.coeff (e - ei)
                  ((1 - MvPowerSeries.C (b : ℝ) * (∑ j : Fin p, MvPowerSeries.X j))⁻¹) := by
            exact le_trans (by positivity)
              (geometricParamZInv_coeff_lower b q (e - ei) hsum_i)
          simpa only [hi] using hcoeff_nonneg
        · simp [hi]
      calc
        (b : ℝ) ^ (q + 1) = (b : ℝ) * (b : ℝ) ^ q := by
          ring
        _ ≤ (b : ℝ) * ∑ i : Fin p,
              if Finsupp.single i 1 ≤ e then
                MvPowerSeries.coeff (e - Finsupp.single i (1 : ℕ))
                  ((1 - MvPowerSeries.C (b : ℝ) * (∑ j : Fin p, MvPowerSeries.X j))⁻¹)
              else
                0 := by
                  refine mul_le_mul_of_nonneg_left ?_ ?_
                  · have hkterm :
                        (b : ℝ) ^ q ≤
                          if ek ≤ e then
                            MvPowerSeries.coeff (e - ek)
                              ((1 - MvPowerSeries.C (b : ℝ) *
                                  (∑ j : Fin p, MvPowerSeries.X j))⁻¹)
                          else
                            0 := by
                              simp [ek, hk_le, hrec]
                    exact le_trans hkterm
                      (Finset.single_le_sum (fun i hi ↦ hnonneg i) (by simp))
                  · positivity
        _ = MvPowerSeries.coeff e
              ((1 - MvPowerSeries.C (b : ℝ) * (∑ j : Fin p, MvPowerSeries.X j))⁻¹) := by
                symm
                exact coeff_geometricParamZInv_eq_sumPred b e he

/-- Helper for Cartan section29 0004_Exercise_2: the positive-degree tail majorant for each linear
coefficient series provides the expected scalar slice bound `M R^{-q}` on every exact pure `z`
coefficient of total degree `q > 0`. -/
lemma linearTailSlice_le_majorant
    (S : RecursiveImplicitSystem 𝕜 n p)
    (M R : NNReal) (hS : S.IsMajorizedBy M R)
    (j i : Fin n) (ez : Fin p →₀ ℕ)
    (hq : 0 < ∑ k : Fin p, ez k) :
    ‖MvPowerSeries.coeff ez (S.linearCoeff j i)‖ ≤
      (M : ℝ) * (R : ℝ)⁻¹ ^ (∑ k : Fin p, ez k) := by
  let q : ℕ := (∑ k : Fin p, ez k) - 1
  have hq' : q + 1 = ∑ k : Fin p, ez k := by
    dsimp [q]
    omega
  have hmem : Finsupp.equivFunOnFinite ez ∈ Finset.finAntidiagonal p (q + 1) := by
    simp [Finset.mem_finAntidiagonal, hq']
  have hsingle :
      ‖MvPowerSeries.coeff ez (S.linearCoeff j i)‖ ≤
        Finset.sum (Finset.finAntidiagonal p (q + 1)) fun e ↦
          ‖MvPowerSeries.coeff (Finsupp.equivFunOnFinite.symm e) (S.linearCoeff j i)‖ := by
    simpa [hmem] using
      (Finset.single_le_sum
        (fun e he ↦ norm_nonneg (MvPowerSeries.coeff (Finsupp.equivFunOnFinite.symm e)
          (S.linearCoeff j i))) hmem :
        ‖MvPowerSeries.coeff
            (Finsupp.equivFunOnFinite.symm (Finsupp.equivFunOnFinite ez)) (S.linearCoeff j i)‖ ≤
          Finset.sum (Finset.finAntidiagonal p (q + 1)) fun e ↦
            ‖MvPowerSeries.coeff (Finsupp.equivFunOnFinite.symm e) (S.linearCoeff j i)‖)
  have hmaj := hS.linearCoeff_tail_norm_isMajorantSeries j i
  calc
    ‖MvPowerSeries.coeff ez (S.linearCoeff j i)‖ ≤
        Finset.sum (Finset.finAntidiagonal p (q + 1)) fun e ↦
          ‖MvPowerSeries.coeff (Finsupp.equivFunOnFinite.symm e) (S.linearCoeff j i)‖ :=
      hsingle
    _ = ‖PowerSeries.coeff (q + 1) (linearTailNormProfile (S.linearCoeff j i))‖ := by
        have hnonnegSum :
            0 ≤
              ∑ e ∈ Finset.finAntidiagonal p (q + 1),
                ‖MvPowerSeries.coeff (Finsupp.equivFunOnFinite.symm e) (S.linearCoeff j i)‖ := by
          exact Finset.sum_nonneg fun e _ ↦
            norm_nonneg (MvPowerSeries.coeff (Finsupp.equivFunOnFinite.symm e) (S.linearCoeff j i))
        have hnonnegCoeff :
            0 ≤ PowerSeries.coeff (q + 1) (linearTailNormProfile (S.linearCoeff j i)) := by
          simpa [linearTailNormProfile] using hnonnegSum
        rw [Real.norm_of_nonneg hnonnegCoeff]
        simp [linearTailNormProfile]
    _ ≤ ((PowerSeries.coeff (q + 1) (linearTailMajorantSeries M R) : NNReal) : ℝ) := by
        simpa [q] using hmaj.coeff_le q
    _ = (M : ℝ) * (R : ℝ)⁻¹ ^ (∑ k : Fin p, ez k) := by
        simpa [hq'] using
          (show ((PowerSeries.coeff (q + 1) (linearTailMajorantSeries M R) : NNReal) : ℝ) =
              (M : ℝ) * (R : ℝ)⁻¹ ^ (q + 1) by
            simp [linearTailMajorantSeries])

/-- Helper for Cartan section29 0004_Exercise_2: the outer scalar majorant factor only depends on
the `z`-variables, so it is obtained by renaming the corresponding pure-`z` geometric series. -/
lemma outerFactor_eq_rename
    (M R : NNReal) :
    ((MvPowerSeries.C (M : ℝ)) *
        (1 - MvPowerSeries.C ((R : ℝ)⁻¹) * paramZSum (n := n) (p := p))⁻¹) =
      MvPowerSeries.rename paramZEmb
        ((MvPowerSeries.C (M : ℝ)) *
          (1 - MvPowerSeries.C ((R : ℝ)⁻¹) *
              ∑ k : Fin p, (MvPowerSeries.X k : MvPowerSeries (Fin p) ℝ))⁻¹) := by
  let base : MvPowerSeries (Fin p) ℝ :=
    1 - MvPowerSeries.C ((R : ℝ)⁻¹) *
      ∑ k : Fin p, (MvPowerSeries.X k : MvPowerSeries (Fin p) ℝ)
  let lifted : MvPowerSeries (ParamIndex n p) ℝ :=
    1 - MvPowerSeries.C ((R : ℝ)⁻¹) * paramZSum (n := n) (p := p)
  have hlifted : MvPowerSeries.rename paramZEmb base = lifted := by
    ext d
    simp [base, lifted, paramZSum, paramZEmb]
  have hlifted0 : MvPowerSeries.constantCoeff lifted ≠ 0 := by
    simp [lifted, paramZSum]
  have hinv : lifted⁻¹ = MvPowerSeries.rename paramZEmb (base⁻¹) := by
    symm
    have hmul :
        MvPowerSeries.rename paramZEmb (base⁻¹) * lifted = 1 := by
      rw [← hlifted, ← map_mul]
      have hbase0 : MvPowerSeries.constantCoeff base ≠ 0 := by
        simp [base]
      simp [base]
    simpa [one_mul] using
      (MvPowerSeries.eq_mul_inv_iff_mul_eq
        (φ₁ := MvPowerSeries.rename paramZEmb (base⁻¹))
        (φ₂ := (1 : MvPowerSeries (ParamIndex n p) ℝ))
        (φ₃ := lifted) hlifted0).2 hmul
  calc
    (MvPowerSeries.C (M : ℝ)) * lifted⁻¹ =
        (MvPowerSeries.C (M : ℝ)) * MvPowerSeries.rename paramZEmb (base⁻¹) := by
          rw [hinv]
    _ = MvPowerSeries.rename paramZEmb ((MvPowerSeries.C (M : ℝ)) * base⁻¹) := by
          simp
    _ = MvPowerSeries.rename paramZEmb
          ((MvPowerSeries.C (M : ℝ)) *
            (1 - MvPowerSeries.C ((R : ℝ)⁻¹) *
                ∑ k : Fin p, (MvPowerSeries.X k : MvPowerSeries (Fin p) ℝ))⁻¹) := by
          simp [base]

/-- Helper for Cartan section29 0004_Exercise_2: on a pure `z` exponent, the outer scalar
majorant factor reads as the coefficient of the underlying geometric `z`-series multiplied by
`M`. -/
lemma outerCoeff_pureZ_eq
    (M R : NNReal) (ez : Fin p →₀ ℕ) :
    MvPowerSeries.coeff (Finsupp.embDomain paramZEmb ez)
      ((MvPowerSeries.C (M : ℝ)) *
        (1 - MvPowerSeries.C ((R : ℝ)⁻¹) * paramZSum (n := n) (p := p))⁻¹) =
      (M : ℝ) *
        MvPowerSeries.coeff ez
          ((1 - MvPowerSeries.C ((R : ℝ)⁻¹) *
              ∑ k : Fin p, (MvPowerSeries.X k : MvPowerSeries (Fin p) ℝ))⁻¹) := by
  rw [outerFactor_eq_rename (n := n) M R]
  simp

/-- Helper for Cartan section29 0004_Exercise_2: the pure `z` coefficients of the outer scalar
majorant factor dominate the scalar geometric weights coming from the source majorant data. -/
lemma outerCoeff_pureZ_lower
    (M R : NNReal) (ez : Fin p →₀ ℕ) :
    (M : ℝ) * (R : ℝ)⁻¹ ^ (∑ k : Fin p, ez k) ≤
      MvPowerSeries.coeff (Finsupp.embDomain paramZEmb ez)
        ((MvPowerSeries.C (M : ℝ)) *
          (1 - MvPowerSeries.C ((R : ℝ)⁻¹) * paramZSum (n := n) (p := p))⁻¹) := by
  rw [outerCoeff_pureZ_eq (n := n) M R ez]
  exact mul_le_mul_of_nonneg_left
    (geometricParamZInv_coeff_lower (R⁻¹) (∑ k : Fin p, ez k) ez rfl) (by positivity)

/-- Helper for Cartan section29 0004_Exercise_2: every linear coefficient series `Γᵢⱼ(z)`,
viewed in the full `(y, z)` variables, is coefficientwise dominated by the common outer scalar
majorant factor. -/
lemma linearCoeff_rename_coeff_le_outer
    (S : RecursiveImplicitSystem 𝕜 n p)
    (M R : NNReal) (hS : S.IsMajorizedBy M R)
    (j i : Fin n) :
    ∀ e : ParamIndex n p →₀ ℕ,
      ‖MvPowerSeries.coeff e
          (MvPowerSeries.rename paramZEmb (S.linearCoeff j i))‖ ≤
        MvPowerSeries.coeff e
          ((MvPowerSeries.C (M : ℝ)) *
            (1 - MvPowerSeries.C ((R : ℝ)⁻¹) * paramZSum (n := n) (p := p))⁻¹)
  | e => by
      classical
      by_cases he : e ∈ Set.range (Finsupp.embDomain paramZEmb)
      · rcases he with ⟨ez, rfl⟩
        by_cases hz0 : ez = 0
        · subst hz0
          rw [MvPowerSeries.coeff_embDomain_rename]
          simpa [paramZSum] using hS.linearCoeff_constant_le j i
        · have hq : 0 < ∑ k : Fin p, ez k := by
            have hneq : (∑ k : Fin p, ez k) ≠ 0 := by
              intro hsum
              apply hz0
              apply Finsupp.ext
              intro k
              have hk : ez k ≤ ∑ t : Fin p, ez t := by
                exact Finset.single_le_sum (fun _ _ ↦ Nat.zero_le _) (by simp)
              rw [hsum] at hk
              exact Nat.eq_zero_of_le_zero hk
            exact Nat.pos_iff_ne_zero.mpr hneq
          rw [MvPowerSeries.coeff_embDomain_rename]
          exact le_trans (linearTailSlice_le_majorant S M R hS j i ez hq)
            (outerCoeff_pureZ_lower (n := n) M R ez)
      · have he' : e ∉ Set.range (Finsupp.mapDomain paramZEmb) := by
          simpa [Finsupp.embDomain_eq_mapDomain] using he
        have hzero :
          MvPowerSeries.coeff e
              (MvPowerSeries.rename paramZEmb (S.linearCoeff j i)) = 0 := by
            exact MvPowerSeries.coeff_rename_eq_zero (f := paramZEmb) (p := S.linearCoeff j i) he'
        have houterzero :
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
        rw [hzero, houterzero]
        simp

/-- Helper for Cartan section29 0004_Exercise_2: fixing the pure `z` exponent `ez`, the
nonlinear source majorant data bounds the entire `x`-degree slice above `ez` by the scalar
weight `M R^{-(qx + |ez|)}`. This is the nonlinear analogue of
`linearTailSlice_le_majorant`. -/
lemma higherCoeffSlice_le_majorantWeight
    (S : RecursiveImplicitSystem 𝕜 n p)
    (M R : NNReal) (hS : S.IsMajorizedBy M R)
    (j : Fin n) (ez : Fin p →₀ ℕ) (qx : ℕ)
    (hqx : 2 ≤ qx) :
    Finset.sum (Finset.finAntidiagonal n qx) (fun ex ↦
      ‖MvPowerSeries.coeff
          (Finsupp.equivFunOnFinite.symm
            (Sum.elim ex (Finsupp.equivFunOnFinite ez) : Fin n ⊕ Fin p → ℕ))
          (S.higher j)‖) ≤
      (M : ℝ) * (R : ℝ)⁻¹ ^ (qx + ∑ k : Fin p, ez k) := by
  let qz : ℕ := ∑ k : Fin p, ez k
  have hmem : Finsupp.equivFunOnFinite ez ∈ Finset.finAntidiagonal p qz := by
    simp [qz]
  have hslice :
      Finset.sum (Finset.finAntidiagonal n qx) (fun ex ↦
        ‖MvPowerSeries.coeff
            (Finsupp.equivFunOnFinite.symm
              (Sum.elim ex (Finsupp.equivFunOnFinite ez) : Fin n ⊕ Fin p → ℕ))
            (S.higher j)‖) ≤
        Finset.sum (Finset.finAntidiagonal n qx) (fun ex ↦
          Finset.sum (Finset.finAntidiagonal p qz) (fun ez' ↦
            ‖MvPowerSeries.coeff
                (Finsupp.equivFunOnFinite.symm
                  (Sum.elim ex ez' : Fin n ⊕ Fin p → ℕ))
                (S.higher j)‖)) := by
    -- Keep the chosen pure-`z` slice and compare it with the full slice sum over all
    -- total-`qz` exponents.
    refine Finset.sum_le_sum ?_
    intro ex hex
    simpa [hmem] using
      (Finset.single_le_sum
        (fun ez' hez' ↦
          norm_nonneg <|
            MvPowerSeries.coeff
              (Finsupp.equivFunOnFinite.symm
                (Sum.elim ex ez' : Fin n ⊕ Fin p → ℕ))
              (S.higher j))
        hmem :
        ‖MvPowerSeries.coeff
            (Finsupp.equivFunOnFinite.symm
              (Sum.elim ex (Finsupp.equivFunOnFinite ez) : Fin n ⊕ Fin p → ℕ))
            (S.higher j)‖ ≤
          Finset.sum (Finset.finAntidiagonal p qz) (fun ez' ↦
            ‖MvPowerSeries.coeff
                (Finsupp.equivFunOnFinite.symm
                  (Sum.elim ex ez' : Fin n ⊕ Fin p → ℕ))
                (S.higher j)‖))
  have hnonneg :
      0 ≤ ((higherNormProfile (S.higher j)).coeffXY qx qz) := by
    rw [MvPowerSeries.coeffXY]
    exact Finset.sum_nonneg fun e he ↦
      norm_nonneg <|
        MvPowerSeries.coeff
          (Finsupp.equivFunOnFinite.symm
            (Sum.elim e.1 e.2 : Fin n ⊕ Fin p → ℕ))
          (S.higher j)
  have hmaj := hS.higher_norm_isMajorantSeries j
  calc
    Finset.sum (Finset.finAntidiagonal n qx) (fun ex ↦
        ‖MvPowerSeries.coeff
            (Finsupp.equivFunOnFinite.symm
              (Sum.elim ex (Finsupp.equivFunOnFinite ez) : Fin n ⊕ Fin p → ℕ))
            (S.higher j)‖) ≤
      Finset.sum (Finset.finAntidiagonal n qx) (fun ex ↦
        Finset.sum (Finset.finAntidiagonal p qz) (fun ez' ↦
          ‖MvPowerSeries.coeff
              (Finsupp.equivFunOnFinite.symm
                (Sum.elim ex ez' : Fin n ⊕ Fin p → ℕ))
              (S.higher j)‖)) :=
      hslice
    _ = ‖(higherNormProfile (S.higher j)).coeffXY qx qz‖ := by
      -- Rewrite the full `(qx, qz)` slice as the corresponding coefficient of
      -- `higherNormProfile`.
      rw [Real.norm_of_nonneg hnonneg, MvPowerSeries.coeffXY, ← Finset.sum_product']
      simp [higherNormProfile, qz]
    _ ≤ (((higherMajorantSeries M R).coeffXY qx qz : NNReal) : ℝ) := by
      simpa using hmaj.coeff_le qx qz
    _ = (M : ℝ) * (R : ℝ)⁻¹ ^ (qx + ∑ k : Fin p, ez k) := by
      rw [MvPowerSeries.coeffXY]
      simp [higherMajorantSeries, qz, hqx]

/-- Helper for Cartan section29 0004_Exercise_2: a finite fiber of higher monomials with fixed
pure `z` part `ez` and fixed `x`-degree `qx` injects into the full `(qx, ez)` slice, so its
source coefficient sum is bounded by the scalar weight attached to that slice. -/
lemma higherCoeffFiber_sum_le_majorantSlice
    (S : RecursiveImplicitSystem 𝕜 n p)
    (M R : NNReal) (hS : S.IsMajorizedBy M R)
    (j : Fin n) (ez : Fin p →₀ ℕ) (qx : ℕ)
    (t : Finset ((Fin n ⊕ Fin p) →₀ ℕ))
    (hqx : 2 ≤ qx)
    (ht :
      ∀ m ∈ t,
        xDegree m = qx ∧
          Finsupp.comapDomain Sum.inr m Sum.inr_injective.injOn = ez) :
    Finset.sum t (fun m ↦ ‖MvPowerSeries.coeff m (S.higher j)‖) ≤
      (M : ℝ) * (R : ℝ)⁻¹ ^ (qx + ∑ k : Fin p, ez k) := by
  classical
  let canon : (Fin n → ℕ) → (Fin n ⊕ Fin p →₀ ℕ) :=
    fun ex ↦
      Finsupp.equivFunOnFinite.symm
        (Sum.elim ex (Finsupp.equivFunOnFinite ez) : Fin n ⊕ Fin p → ℕ)
  have hcanon_inj : Function.Injective canon := by
    intro ex₁ ex₂ hEq
    funext i
    -- The left coordinates of the canonical `(x, z)` monomial recover the original `x`-slice.
    have hval :=
      congrArg (fun m : (Fin n ⊕ Fin p →₀ ℕ) => m (Sum.inl i)) hEq
    simpa [canon] using hval
  have hsubset : t ⊆ (Finset.finAntidiagonal n qx).image canon := by
    intro m hm
    rcases ht m hm with ⟨hmxdeg, hmz⟩
    let mx : Fin n →₀ ℕ :=
      Finsupp.comapDomain Sum.inl m Sum.inl_injective.injOn
    have hmxsum : mx.sum (fun _ q ↦ q) = xDegree m := by
      -- The `x`-part of `m` records exactly the total `x`-degree.
      rw [Finsupp.sum]
      refine Finset.sum_subset (by simp) ?_
      intro i _ hi
      have hi' : Sum.inl i ∉ m.support := by
        simpa using hi
      simpa [mx, xDegree, Finsupp.mem_support_iff] using hi'
    have hmxmem : Finsupp.equivFunOnFinite mx ∈ Finset.finAntidiagonal n qx := by
      simpa [Finset.mem_finAntidiagonal, hmxsum, hmxdeg]
    refine Finset.mem_image.mpr ?_
    refine ⟨Finsupp.equivFunOnFinite mx, hmxmem, ?_⟩
    have hcanon_mx :
        canon (Finsupp.equivFunOnFinite mx) = mx.sumElim ez := by
      ext s
      cases s with
      | inl i => simp [canon]
      | inr k => simp [canon]
    have hmdecomp : mx.sumElim ez = m := by
      -- Fixing the pure `z` part leaves the pure `x` part as the only remaining datum.
      simpa [mx, hmz] using Finsupp.comapDomain_sumElim_comapDomain m
    exact hcanon_mx.trans hmdecomp
  have hfiber_le :
      Finset.sum t (fun m ↦ ‖MvPowerSeries.coeff m (S.higher j)‖) ≤
        Finset.sum ((Finset.finAntidiagonal n qx).image canon)
          (fun m ↦ ‖MvPowerSeries.coeff m (S.higher j)‖) := by
    -- Compare the finite fiber with the larger canonical slice support.
    exact Finset.sum_le_sum_of_subset_of_nonneg hsubset
      (fun m _ _ ↦ norm_nonneg _)
  have hslice :
      Finset.sum ((Finset.finAntidiagonal n qx).image canon)
          (fun m ↦ ‖MvPowerSeries.coeff m (S.higher j)‖) =
        Finset.sum (Finset.finAntidiagonal n qx) (fun ex ↦
          ‖MvPowerSeries.coeff
              (Finsupp.equivFunOnFinite.symm
                (Sum.elim ex (Finsupp.equivFunOnFinite ez) : Fin n ⊕ Fin p → ℕ))
              (S.higher j)‖) := by
    -- Re-express the image sum back on the canonical antidiagonal owner.
    rw [Finset.sum_image hcanon_inj.injOn]
  calc
    Finset.sum t (fun m ↦ ‖MvPowerSeries.coeff m (S.higher j)‖) ≤
        Finset.sum ((Finset.finAntidiagonal n qx).image canon)
          (fun m ↦ ‖MvPowerSeries.coeff m (S.higher j)‖) :=
      hfiber_le
    _ = Finset.sum (Finset.finAntidiagonal n qx) (fun ex ↦
          ‖MvPowerSeries.coeff
              (Finsupp.equivFunOnFinite.symm
                (Sum.elim ex (Finsupp.equivFunOnFinite ez) : Fin n ⊕ Fin p → ℕ))
              (S.higher j)‖) := hslice
    _ ≤ (M : ℝ) * (R : ℝ)⁻¹ ^ (qx + ∑ k : Fin p, ez k) :=
      higherCoeffSlice_le_majorantWeight (n := n) (p := p) S M R hS j ez qx hqx


end ScalarQuadraticMajorantExistence
