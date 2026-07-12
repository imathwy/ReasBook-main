import StacksProject_2024.Chap10.Example_10_119_5.CoefficientSubring

noncomputable section

universe u

open PowerSeries IsLocalRing
open AdicCompletion
open scoped Pointwise

variable (k : Type u) [Field k] (p : ℕ) [Fact p.Prime] [ExpChar k p]

open scoped PthPowerSubfield

local notation "A" => finitePthPowerCoefficientSubring k p

omit [Fact p.Prime] in
/-- Helper for Chap10 Example 10 119 5: inverse coefficients of a series with nonzero constant
coefficient still lie in the same coefficient-generated intermediate field. -/
lemma coeff_inv_mem_coefficientAdjoinOverPthPowers {f : PowerSeries k}
    (hf0 : PowerSeries.constantCoeff f ≠ 0) (n : ℕ) :
    PowerSeries.coeff n f⁻¹ ∈ coefficientAdjoinOverPthPowers k p f := by
  -- Lift `f` to a power series over its generated coefficient field.
  let L := coefficientAdjoinOverPthPowers k p f
  let fL : PowerSeries L := PowerSeries.mk fun n ↦
    ⟨PowerSeries.coeff n f, coeff_mem_coefficientAdjoinOverPthPowers k p f n⟩
  have hfL_map : PowerSeries.map L.val.toRingHom fL = f := by
    ext m
    simp [fL, PowerSeries.coeff_map]
  have hfL0 : PowerSeries.constantCoeff fL ≠ 0 := by
    intro h
    apply hf0
    have hval := congrArg (fun x : L => (x : k)) h
    simpa [fL, PowerSeries.coeff_zero_eq_constantCoeff_apply] using hval
  -- Inversion commutes with the inclusion after checking the defining inverse equation.
  have hmap_inv : PowerSeries.map L.val.toRingHom fL⁻¹ = f⁻¹ := by
    rw [PowerSeries.eq_inv_iff_mul_eq_one hf0]
    rw [← hfL_map]
    simpa using
      congrArg (fun φ : PowerSeries L ↦ PowerSeries.map L.val.toRingHom φ)
        (PowerSeries.inv_mul_cancel fL hfL0)
  have hcoeff : L.val.toRingHom (PowerSeries.coeff n fL⁻¹) = PowerSeries.coeff n f⁻¹ := by
    calc
      L.val.toRingHom (PowerSeries.coeff n fL⁻¹) =
          PowerSeries.coeff n (PowerSeries.map L.val.toRingHom fL⁻¹) := by
        simp [PowerSeries.coeff_map]
      _ = PowerSeries.coeff n f⁻¹ := by rw [hmap_inv]
  -- The coefficient of the lifted inverse is an element of `L`, so its image is in `L`.
  exact hcoeff ▸ (PowerSeries.coeff n fL⁻¹).2

omit [Fact p.Prime] in
/-- Helper for Chap10 Example 10 119 5: coefficient-field finiteness is closed under inverses
of power series with nonzero constant coefficient. -/
lemma hasFinitePthPowerCoefficientField_inv_of_constantCoeff_ne_zero {f : PowerSeries k}
    (hf : HasFinitePthPowerCoefficientField k p f)
    (hf0 : PowerSeries.constantCoeff f ≠ 0) :
    HasFinitePthPowerCoefficientField k p f⁻¹ := by
  -- Use the same generated intermediate field and the coefficientwise inverse-closure lemma.
  let L := coefficientAdjoinOverPthPowers k p f
  letI : FiniteDimensional (k^[p]) L := hf
  exact hasFinitePthPowerCoefficientField_of_coeff_mem k p f⁻¹ L
    (coeff_inv_mem_coefficientAdjoinOverPthPowers k p hf0)

omit [Fact p.Prime] in
/-- Helper for Chap10 Example 10 119 5: an ambient power-series unit lying in the coefficient
subring is a unit of the coefficient subring. -/
lemma finitePthPowerCoefficientSubring_isUnit_of_constantCoeff_ne_zero {f : PowerSeries k}
    (hf : f ∈ A) (hf0 : PowerSeries.constantCoeff f ≠ 0) :
    IsUnit (⟨f, hf⟩ : ↥A) := by
  -- The inverse also lies in `A`, so the ambient inverse equations define a subtype unit.
  have hinv : f⁻¹ ∈ A :=
    hasFinitePthPowerCoefficientField_inv_of_constantCoeff_ne_zero k p hf hf0
  refine ⟨⟨⟨f, hf⟩, ⟨f⁻¹, hinv⟩, ?_, ?_⟩, rfl⟩
  · exact Subtype.ext (PowerSeries.mul_inv_cancel f hf0)
  · exact Subtype.ext (PowerSeries.inv_mul_cancel f hf0)

omit [Fact p.Prime] in
/-- Helper for Chap10 Example 10 119 5: the power-series uniformizer remains irreducible in the
coefficient subring. -/
lemma finitePthPowerCoefficientSubring_X_irreducible :
    Irreducible (⟨PowerSeries.X, X_mem_finitePthPowerCoefficientSubring k p⟩ : ↥A) := by
  -- Test unit and factorization questions after embedding the subtype into `k[[X]]`.
  refine ⟨?_, ?_⟩
  · intro hunit
    have hamb : IsUnit (PowerSeries.X : PowerSeries k) := by
      rcases hunit with ⟨u, hu⟩
      refine ⟨Units.map (algebraMap ↥A (PowerSeries k)) u, ?_⟩
      exact congrArg (fun z : ↥A => (z : PowerSeries k)) hu
    exact PowerSeries.X_irreducible.not_isUnit hamb
  · intro a b hfactor
    have hamb : (PowerSeries.X : PowerSeries k) = (a : PowerSeries k) * (b : PowerSeries k) := by
      exact congrArg (fun z : ↥A => (z : PowerSeries k)) hfactor
    rcases PowerSeries.X_irreducible.isUnit_or_isUnit hamb with ha | hb
    · left
      have ha0 : PowerSeries.constantCoeff (a : PowerSeries k) ≠ 0 :=
        (PowerSeries.isUnit_iff_constantCoeff.mp ha).ne_zero
      exact finitePthPowerCoefficientSubring_isUnit_of_constantCoeff_ne_zero k p a.2 ha0
    · right
      have hb0 : PowerSeries.constantCoeff (b : PowerSeries k) ≠ 0 :=
        (PowerSeries.isUnit_iff_constantCoeff.mp hb).ne_zero
      exact finitePthPowerCoefficientSubring_isUnit_of_constantCoeff_ne_zero k p b.2 hb0

-- Proof sketch: use the `x`-adic valuation on `k[[x]]`; the coefficient-field finiteness
-- condition is preserved under the valuation-ring operations, and the resulting subring is exactly
-- the valuation ring of the induced discrete valuation.
omit [Fact p.Prime] in
/-- Helper for Chap10 Example 10 119 5: elements of the coefficient subring factor as a unit
times a power of the uniformizer `X`. -/
lemma finitePthPowerCoefficientSubring_hasUnitMulPowIrreducibleFactorization :
    IsDiscreteValuationRing.HasUnitMulPowIrreducibleFactorization ↥A := by
  -- Use the same uniformizer as `k[[X]]` and keep the unit factor inside `A`.
  let ϖ : ↥A := ⟨PowerSeries.X, X_mem_finitePthPowerCoefficientSubring k p⟩
  refine ⟨ϖ, finitePthPowerCoefficientSubring_X_irreducible k p, ?_⟩
  intro x hx
  have hx_ambient : (x : PowerSeries k) ≠ 0 := by
    intro hzero
    apply hx
    exact Subtype.ext hzero
  let uSeries : PowerSeries k := PowerSeries.divXPowOrder (x : PowerSeries k)
  have hu_mem : uSeries ∈ A :=
    divXPowOrder_mem_finitePthPowerCoefficientSubring k p x.2
  have hu0 : PowerSeries.constantCoeff uSeries ≠ 0 := by
    have hdiv :
        PowerSeries.constantCoeff
            (PowerSeries.divXPowOrder (x : PowerSeries k)) ≠ 0 := by
      intro hzero
      exact hx_ambient (PowerSeries.constantCoeff_divXPowOrder_eq_zero_iff.mp hzero)
    simpa [uSeries] using hdiv
  obtain ⟨u, hu⟩ :=
    finitePthPowerCoefficientSubring_isUnit_of_constantCoeff_ne_zero k p hu_mem hu0
  -- The ambient `X`-adic factorization becomes an equality in the subtype by extensionality.
  refine ⟨(x : PowerSeries k).order.toNat, ⟨u, ?_⟩⟩
  exact Subtype.ext <| by
    simpa [ϖ, uSeries, hu] using
      (PowerSeries.X_pow_order_mul_divXPowOrder (f := (x : PowerSeries k)))

omit [Fact p.Prime] in
/-- The coefficient subring `A` is a discrete valuation ring. -/
theorem finitePthPowerCoefficientSubring_isDiscreteValuationRing :
    IsDiscreteValuationRing ↥A := by
  -- The source DVR argument is exactly the unit-times-uniformizer-power criterion.
  exact IsDiscreteValuationRing.ofHasUnitMulPowIrreducibleFactorization
    (finitePthPowerCoefficientSubring_hasUnitMulPowIrreducibleFactorization k p)

/-- The coefficient subring inherits its canonical discrete valuation ring structure. -/
instance : IsDiscreteValuationRing ↥A :=
  finitePthPowerCoefficientSubring_isDiscreteValuationRing k p

omit [Fact p.Prime] in
/-- Helper for Chap10 Example 10 119 5: the coefficient DVR has Krull dimension one. -/
lemma finitePthPowerCoefficientSubring_ringKrullDim_eq_one :
    ringKrullDim ↥A = 1 := by
  -- A DVR is a non-field PID, so mathlib's PID dimension theorem applies.
  exact IsPrincipalIdealRing.ringKrullDim_eq_one ↥A
    (IsDiscreteValuationRing.not_isField (R := ↥A))

/-- The induced fraction-field algebra `Frac(A) → Frac(k[[x]])`. -/
noncomputable instance finitePthPowerCoefficientSubring_fractionRingAlgebra :
    Algebra (FractionRing ↥A) (FractionRing (PowerSeries k)) :=
  RingHom.toAlgebra
    (IsFractionRing.map
      (show Function.Injective (algebraMap ↥A (PowerSeries k)) from fun _ _ h ↦ Subtype.ext h))

-- Proof sketch: every ambient power series is integral over `A` because its `p`th power lies in
-- `A`; injectivity of the subtype map then makes the integral inclusion a local homomorphism.
/-- Helper for Chap10 Example 10 119 5: the inclusion `A → k[[X]]` is a local homomorphism. -/
theorem finitePthPowerCoefficientSubring_algebraMap_isLocalHom :
    IsLocalHom (algebraMap ↥A (PowerSeries k)) := by
  -- Package the pointwise integrality result as integrality of the whole ambient algebra.
  have hIntegral : Algebra.IsIntegral ↥A (PowerSeries k) :=
    ⟨finitePthPowerCoefficientAdjoinSubring_isIntegral k p⟩
  have hInjective : Function.Injective (algebraMap ↥A (PowerSeries k)) := by
    intro x y h
    exact Subtype.ext h
  -- Integral injective maps reflect units, which is exactly the local-hom condition.
  exact (algebraMap_isIntegral_iff.mpr hIntegral).isLocalHom hInjective

/-- Helper for Chap10 Example 10 119 5: every element of `k` is integral over the subfield
`k^p`. -/
lemma isIntegral_over_pthPowerSubfield (c : k) :
    IsIntegral (k^[p]) c := by
  -- The `p`th power of `c` lies in the Frobenius range, so `c` is integral by the power criterion.
  have hp_pos : 0 < p := (Fact.out : p.Prime).pos
  let cp : k^[p] :=
    ⟨c ^ p, RingHom.mem_fieldRange_self (frobenius k p) c⟩
  have hpow : IsIntegral (k^[p]) (c ^ p) := by
    simpa [cp] using
      (isIntegral_algebraMap : IsIntegral (k^[p]) (algebraMap (k^[p]) k cp))
  exact IsIntegral.of_pow hp_pos hpow

omit [Fact p.Prime] in
/-- Helper for Chap10 Example 10 119 5: coefficient-field finiteness is stable under shifting
the coefficient sequence. -/
lemma hasFinitePthPowerCoefficientField_shift {f : PowerSeries k}
    (hf : HasFinitePthPowerCoefficientField k p f) (n : ℕ) :
    HasFinitePthPowerCoefficientField k p
      (PowerSeries.mk fun i ↦ PowerSeries.coeff (i + n) f) := by
  -- The shifted coefficients are still coefficients of the original finite generated field.
  let L := coefficientAdjoinOverPthPowers k p f
  letI : FiniteDimensional (k^[p]) L := hf
  exact hasFinitePthPowerCoefficientField_of_coeff_mem k p
    (PowerSeries.mk fun i ↦ PowerSeries.coeff (i + n) f) L (by
      intro i
      simpa [PowerSeries.coeff_mk] using
        coeff_mem_coefficientAdjoinOverPthPowers k p f (i + n))

/-- Helper for Chap10 Example 10 119 5: every polynomial truncation of an ambient power series
belongs to the coefficient subring. -/
lemma finitePthPowerCoefficientSubring_trunc_mem (f : PowerSeries k) (n : ℕ) :
    ((PowerSeries.trunc n f : Polynomial k) : PowerSeries k) ∈ A := by
  -- The truncation has only finitely many possible nonzero coefficients, and each is integral over
  -- `k^p`; the finite adjoin of those coefficients certifies membership in `A`.
  let T : Set k :=
    Set.insert 0 (Set.range fun i : Fin n ↦ PowerSeries.coeff (i : ℕ) f)
  have hTfinite : T.Finite :=
    (Set.finite_range fun i : Fin n ↦ PowerSeries.coeff (i : ℕ) f).insert 0
  letI : Finite T := hTfinite
  let L : IntermediateField (k^[p]) k := IntermediateField.adjoin (k^[p]) T
  haveI : FiniteDimensional (k^[p]) L :=
    IntermediateField.finiteDimensional_adjoin (K := k^[p]) (L := k) (S := T) (by
      intro c _hc
      exact isIntegral_over_pthPowerSubfield k p c)
  refine hasFinitePthPowerCoefficientField_of_coeff_mem k p _ L ?_
  intro m
  refine IntermediateField.subset_adjoin (F := k^[p]) (S := T) ?_
  dsimp [T]
  by_cases hm : m < n
  · right
    refine ⟨⟨m, hm⟩, ?_⟩
    simp [PowerSeries.coeff_trunc, hm]
  · left
    simp [PowerSeries.coeff_trunc, hm]

/-- Helper for Chap10 Example 10 119 5: membership in `(X)^n` is detected by vanishing of the
first `n` coefficients of a power series. -/
private lemma coefficientPowerSeries_mem_span_X_pow_iff_coeff_eq_zero
    (n : ℕ) (f : PowerSeries k) :
    f ∈ (Ideal.span ({(PowerSeries.X : PowerSeries k)} : Set (PowerSeries k))) ^ n ↔
      ∀ m, m < n → PowerSeries.coeff m f = 0 := by
  -- Rewrite `(X)^n` as a principal ideal and use the standard divisibility criterion.
  rw [Ideal.span_singleton_pow, Ideal.mem_span_singleton, PowerSeries.X_pow_dvd_iff]

/-- Helper for Chap10 Example 10 119 5: congruence modulo `(X)^n` is coefficientwise equality
below degree `n`. -/
private lemma coefficientPowerSeries_smodEq_span_X_pow_iff_coeff_eq
    (n : ℕ) (f g : PowerSeries k) :
    f ≡ g
      [SMOD ((Ideal.span ({(PowerSeries.X : PowerSeries k)} : Set (PowerSeries k))) ^ n •
        (⊤ : Submodule (PowerSeries k) (PowerSeries k)))] ↔
      ∀ m, m < n → PowerSeries.coeff m f = PowerSeries.coeff m g := by
  -- Convert modular equality to membership of the difference and read off coefficients.
  rw [SModEq.sub_mem, smul_eq_mul, Ideal.mul_top,
    coefficientPowerSeries_mem_span_X_pow_iff_coeff_eq_zero (k := k) (n := n) (f := f - g)]
  constructor
  · intro h m hm
    simpa [sub_eq_zero] using h m hm
  · intro h m hm
    simpa [h m hm] using h m hm

omit [Fact p.Prime] in
/-- Helper for Chap10 Example 10 119 5: the maximal-ideal filtration on `A` is the ambient
coefficientwise `X`-adic filtration. -/
lemma finitePthPowerCoefficientSubring_mem_maximalIdeal_pow_iff_coeff_eq_zero
    (a : ↥A) (n : ℕ) :
    a ∈ (maximalIdeal ↥A) ^ n ↔
      ∀ m, m < n → PowerSeries.coeff m (a : PowerSeries k) = 0 := by
  -- Replace the maximal ideal of the DVR `A` by the span of the same uniformizer `X`.
  let ϖ : ↥A := ⟨PowerSeries.X, X_mem_finitePthPowerCoefficientSubring k p⟩
  have hmax : maximalIdeal ↥A = Ideal.span ({ϖ} : Set ↥A) :=
    (finitePthPowerCoefficientSubring_X_irreducible k p).maximalIdeal_eq
  constructor
  · intro ha
    -- Divisibility by the subtype uniformizer gives ambient divisibility by `X^n`.
    have hdiv : (PowerSeries.X : PowerSeries k) ^ n ∣ (a : PowerSeries k) := by
      rw [hmax, Ideal.span_singleton_pow, Ideal.mem_span_singleton] at ha
      rcases ha with ⟨b, hb⟩
      refine ⟨(b : PowerSeries k), ?_⟩
      exact congrArg (fun z : ↥A ↦ (z : PowerSeries k)) hb
    exact (PowerSeries.X_pow_dvd_iff (R := k) (n := n) (φ := (a : PowerSeries k))).1 hdiv
  · intro hcoeff
    -- The coefficient vanishing writes the series as `X^n` times its shifted tail; the tail remains
    -- in `A` by the shift lemma.
    rw [hmax, Ideal.span_singleton_pow, Ideal.mem_span_singleton]
    let tail : PowerSeries k :=
      PowerSeries.mk fun i ↦ PowerSeries.coeff (i + n) (a : PowerSeries k)
    have htail_mem : tail ∈ A :=
      hasFinitePthPowerCoefficientField_shift k p a.2 n
    refine ⟨(⟨tail, htail_mem⟩ : ↥A), ?_⟩
    apply Subtype.ext
    have htrunc_zero : ((PowerSeries.trunc n (a : PowerSeries k) : Polynomial k) :
        PowerSeries k) = 0 := by
      ext m
      by_cases hm : m < n
      · simp [PowerSeries.coeff_trunc, hm, hcoeff m hm]
      · simp [PowerSeries.coeff_trunc, hm]
    have hdecomp := PowerSeries.eq_X_pow_mul_shift_add_trunc (R := k) n (a : PowerSeries k)
    have hamb : (a : PowerSeries k) = PowerSeries.X ^ n * tail := by
      simpa [tail, htrunc_zero] using hdecomp
    exact hamb

omit [Fact p.Prime] in
/-- Helper for Chap10 Example 10 119 5: equality of ambient `X`-adic quotient classes for two
elements of `A` descends to equality in the corresponding quotient of `A`. -/
private lemma finitePthPowerCoefficientSubring_quotient_mk_eq_of_ambient {a b : ↥A} {n : ℕ}
    (h : Ideal.Quotient.mk ((maximalIdeal (PowerSeries k)) ^ n) (a : PowerSeries k) =
      Ideal.Quotient.mk ((maximalIdeal (PowerSeries k)) ^ n) (b : PowerSeries k)) :
    Ideal.Quotient.mk ((maximalIdeal ↥A) ^ n) a =
      Ideal.Quotient.mk ((maximalIdeal ↥A) ^ n) b := by
  -- Convert both quotient equalities to membership of the difference in the corresponding
  -- filtration, then use the coefficient-filtration bridge.
  rw [Ideal.Quotient.mk_eq_mk_iff_sub_mem] at h ⊢
  rw [finitePthPowerCoefficientSubring_mem_maximalIdeal_pow_iff_coeff_eq_zero k p (a - b) n]
  have hamb : (a : PowerSeries k) - (b : PowerSeries k) ∈
      (Ideal.span ({(PowerSeries.X : PowerSeries k)} : Set (PowerSeries k))) ^ n := by
    simpa [PowerSeries.maximalIdeal_eq_span_X] using h
  exact
    (coefficientPowerSeries_mem_span_X_pow_iff_coeff_eq_zero (k := k) (n := n)
      (f := (a : PowerSeries k) - (b : PowerSeries k))).1 hamb

/-- Helper for Chap10 Example 10 119 5: the power-series ring is complete for the `(X)`-adic
topology. -/
private theorem coefficientPowerSeries_isAdicComplete_span_X :
    IsAdicComplete (Ideal.span ({(PowerSeries.X : PowerSeries k)} : Set (PowerSeries k)))
      (PowerSeries k) := by
  -- Build the completion witness directly from stabilized coefficients.
  refine
    { haus' := ?_
      prec' := ?_ }
  · intro f h
    ext n
    have hmem :
        f ∈ (Ideal.span ({(PowerSeries.X : PowerSeries k)} : Set (PowerSeries k))) ^
          (n + 1) := by
      simpa [SModEq.zero, smul_eq_mul, Ideal.mul_top] using h (n + 1)
    exact
      (coefficientPowerSeries_mem_span_X_pow_iff_coeff_eq_zero
        (k := k) (n := n + 1) (f := f)).1 hmem n (Nat.lt_succ_self n)
  · intro x h
    refine ⟨PowerSeries.mk (fun n ↦ PowerSeries.coeff n (x (n + 1))), ?_⟩
    intro n
    -- The Cauchy condition identifies every coefficient below `n` with its stabilized value.
    rw [coefficientPowerSeries_smodEq_span_X_pow_iff_coeff_eq (k := k) (n := n)]
    intro i hi
    have hmod :
        x (i + 1) ≡ x n
          [SMOD ((Ideal.span ({(PowerSeries.X : PowerSeries k)} : Set (PowerSeries k))) ^
            (i + 1) • (⊤ : Submodule (PowerSeries k) (PowerSeries k)))] :=
      h (Nat.succ_le_of_lt hi)
    have hstable :
        PowerSeries.coeff i (x (i + 1)) = PowerSeries.coeff i (x n) :=
      (coefficientPowerSeries_smodEq_span_X_pow_iff_coeff_eq
        (k := k) (n := i + 1) (f := x (i + 1)) (g := x n)).1
        hmod i (Nat.lt_succ_self i)
    simpa [PowerSeries.coeff_mk] using hstable.symm

section SourceFacing

local instance :
    IsLocalHom (algebraMap ↥A (PowerSeries k)) :=
  finitePthPowerCoefficientSubring_algebraMap_isLocalHom k p

local instance : IsAdicComplete (maximalIdeal (PowerSeries k)) (PowerSeries k) :=
  by
    -- The maximal ideal of `k[[X]]` is `(X)`, and the coefficientwise construction above is
    -- complete for that ideal.
    simpa [PowerSeries.maximalIdeal_eq_span_X] using
      coefficientPowerSeries_isAdicComplete_span_X (k := k)

/-- Helper for Chap10 Example 10 119 5: the raw completion comparison map respects the
coefficient-subring algebra structures. -/
private theorem finitePthPowerCoefficientSubringCompletionAlgHom_commutes
    (a : ↥A) :
    (((AdicCompletion.ofAlgEquiv (maximalIdeal (PowerSeries k))).symm.toRingHom.comp
        (maximalIdealCompletionMap (algebraMap ↥A (PowerSeries k))))
      (algebraMap ↥A (AdicCompletion (maximalIdeal ↥A) ↥A) a)) =
        algebraMap ↥A (PowerSeries k) a := by
  -- The functorial completion map extends the original inclusion on dense source elements.
  have hmap :
      maximalIdealCompletionMap (algebraMap ↥A (PowerSeries k))
          (AdicCompletion.of (maximalIdeal ↥A) ↥A a) =
        AdicCompletion.of (maximalIdeal (PowerSeries k)) (PowerSeries k)
          (algebraMap ↥A (PowerSeries k) a) := by
    have hcomp := RingHom.congr_fun
      (maximalIdealCompletionMap_comp (algebraMap ↥A (PowerSeries k))) a
    simpa using hcomp
  -- The ambient power-series ring is identified with its own completion.
  calc
    (((AdicCompletion.ofAlgEquiv (maximalIdeal (PowerSeries k))).symm.toRingHom.comp
        (maximalIdealCompletionMap (algebraMap ↥A (PowerSeries k))))
      (algebraMap ↥A (AdicCompletion (maximalIdeal ↥A) ↥A) a))
        =
      (AdicCompletion.ofAlgEquiv (maximalIdeal (PowerSeries k))).symm
        (maximalIdealCompletionMap (algebraMap ↥A (PowerSeries k))
          (AdicCompletion.of (maximalIdeal ↥A) ↥A a)) := by
        rfl
    _ =
      (AdicCompletion.ofAlgEquiv (maximalIdeal (PowerSeries k))).symm
        (AdicCompletion.of (maximalIdeal (PowerSeries k)) (PowerSeries k)
          (algebraMap ↥A (PowerSeries k) a)) := by
        rw [hmap]
    _ = algebraMap ↥A (PowerSeries k) a :=
        AdicCompletion.ofAlgEquiv_symm_of (I := maximalIdeal (PowerSeries k))
          (x := algebraMap ↥A (PowerSeries k) a)

/-- Helper for Chap10 Example 10 119 5: the raw map from the coefficient-ring completion to
`k[[X]]`. -/
private noncomputable def finitePthPowerCoefficientSubringCompletionAlgHom :
    AdicCompletion (maximalIdeal ↥A) ↥A →ₐ[↥A] PowerSeries k :=
  { toRingHom :=
      ((AdicCompletion.ofAlgEquiv (maximalIdeal (PowerSeries k))).symm.toRingHom.comp
        (maximalIdealCompletionMap (algebraMap ↥A (PowerSeries k))))
    commutes' := finitePthPowerCoefficientSubringCompletionAlgHom_commutes k p }

/-- Helper for Chap10 Example 10 119 5: the raw completion comparison fixes dense
coefficient-subring elements. -/
private theorem finitePthPowerCoefficientSubringCompletionAlgHom_of
    (a : ↥A) :
    finitePthPowerCoefficientSubringCompletionAlgHom k p
      (AdicCompletion.of (maximalIdeal ↥A) ↥A a) = a := by
  -- This is the algebra-compatibility computation with the two algebra maps unfolded.
  simpa [finitePthPowerCoefficientSubringCompletionAlgHom] using
    finitePthPowerCoefficientSubringCompletionAlgHom_commutes k p a

/-- Helper for Chap10 Example 10 119 5: the raw completion comparison is bijective. -/
private theorem finitePthPowerCoefficientSubringCompletionAlgHom_bijective :
    Function.Bijective (finitePthPowerCoefficientSubringCompletionAlgHom k p) := by
  -- Compare completion elements stagewise.  The key bridge is that quotients of `A` and of
  -- `k[[X]]` have the same coefficient classes below the chosen stage.
  constructor
  · intro x y hxy
    revert y
    let P : AdicCompletion (maximalIdeal ↥A) ↥A → Prop :=
      fun x₀ ↦ ∀ y₀,
        finitePthPowerCoefficientSubringCompletionAlgHom k p x₀ =
          finitePthPowerCoefficientSubringCompletionAlgHom k p y₀ → x₀ = y₀
    change P x
    refine AdicCompletion.induction_on (I := maximalIdeal ↥A) (M := ↥A) x ?_
    intro rx y₀ hxy₀
    revert hxy₀
    let Q : AdicCompletion (maximalIdeal ↥A) ↥A → Prop :=
      fun y₁ ↦
        finitePthPowerCoefficientSubringCompletionAlgHom k p
            (AdicCompletion.mk (maximalIdeal ↥A) ↥A rx) =
          finitePthPowerCoefficientSubringCompletionAlgHom k p y₁ →
          AdicCompletion.mk (maximalIdeal ↥A) ↥A rx = y₁
    change Q y₀
    refine AdicCompletion.induction_on (I := maximalIdeal ↥A) (M := ↥A) y₀ ?_
    intro ry hxy₁
    apply AdicCompletion.ext_evalₐ
    intro n
    have hcompletion :
        maximalIdealCompletionMap (algebraMap ↥A (PowerSeries k))
            (AdicCompletion.mk (maximalIdeal ↥A) ↥A rx) =
          maximalIdealCompletionMap (algebraMap ↥A (PowerSeries k))
            (AdicCompletion.mk (maximalIdeal ↥A) ↥A ry) := by
      -- Applying the ambient completion map cancels the final `ofAlgEquiv.symm`.
      have hof :=
        congrArg (AdicCompletion.of (maximalIdeal (PowerSeries k)) (PowerSeries k)) hxy₁
      simpa [finitePthPowerCoefficientSubringCompletionAlgHom] using hof
    have hstage :=
      congrArg (AdicCompletion.evalₐ (maximalIdeal (PowerSeries k)) n) hcompletion
    rw [maximalIdealCompletionMap_evalₐ_mk, maximalIdealCompletionMap_evalₐ_mk] at hstage
    rw [AdicCompletion.evalₐ_mk, AdicCompletion.evalₐ_mk]
    exact finitePthPowerCoefficientSubring_quotient_mk_eq_of_ambient k p hstage
  · intro f
    -- Approximate `f` by its polynomial truncations, which all lie in `A`.
    let truncA : ℕ → ↥A :=
      fun n ↦
        ⟨((PowerSeries.trunc n f : Polynomial k) : PowerSeries k),
          finitePthPowerCoefficientSubring_trunc_mem k p f n⟩
    have htrunc_cauchy :
        ∀ n, truncA n ≡ truncA (n + 1)
          [SMOD ((maximalIdeal ↥A) ^ n • (⊤ : Submodule ↥A ↥A))] := by
      intro n
      rw [SModEq.sub_mem, smul_eq_mul, Ideal.mul_top]
      rw [finitePthPowerCoefficientSubring_mem_maximalIdeal_pow_iff_coeff_eq_zero k p]
      intro m hm
      have hms : m < n + 1 := Nat.lt_trans hm (Nat.lt_succ_self n)
      simp [truncA, PowerSeries.coeff_trunc, hm, hms]
    let r : AdicCauchySequence (maximalIdeal ↥A) ↥A :=
      AdicCauchySequence.mk (maximalIdeal ↥A) ↥A truncA htrunc_cauchy
    refine ⟨AdicCompletion.mk (maximalIdeal ↥A) ↥A r, ?_⟩
    -- After applying the ambient completion equivalence, the stage-`n` comparison says that
    -- `trunc n f` and `f` have the same quotient class modulo `X^n`.
    apply (AdicCompletion.ofAlgEquiv (maximalIdeal (PowerSeries k))).injective
    apply AdicCompletion.ext_evalₐ
    intro n
    calc
      AdicCompletion.evalₐ (maximalIdeal (PowerSeries k)) n
          ((AdicCompletion.ofAlgEquiv (maximalIdeal (PowerSeries k)))
            (finitePthPowerCoefficientSubringCompletionAlgHom k p
              (AdicCompletion.mk (maximalIdeal ↥A) ↥A r))) =
        AdicCompletion.evalₐ (maximalIdeal (PowerSeries k)) n
          (maximalIdealCompletionMap (algebraMap ↥A (PowerSeries k))
            (AdicCompletion.mk (maximalIdeal ↥A) ↥A r)) := by
          dsimp [finitePthPowerCoefficientSubringCompletionAlgHom]
          exact
            AdicCompletion.mk_ofAlgEquiv_symm (I := maximalIdeal (PowerSeries k)) n
              (maximalIdealCompletionMap (algebraMap ↥A (PowerSeries k))
                (AdicCompletion.mk (maximalIdeal ↥A) ↥A r))
      _ = Ideal.Quotient.mk ((maximalIdeal (PowerSeries k)) ^ n)
          ((algebraMap ↥A (PowerSeries k)) (r.val n)) := by
          exact maximalIdealCompletionMap_evalₐ_mk (algebraMap ↥A (PowerSeries k)) n r
      _ = Ideal.Quotient.mk ((maximalIdeal (PowerSeries k)) ^ n) f := by
          rw [Ideal.Quotient.mk_eq_mk_iff_sub_mem]
          have hmem_span :
              (algebraMap ↥A (PowerSeries k) (r.val n) - f) ∈
                (Ideal.span ({(PowerSeries.X : PowerSeries k)} : Set (PowerSeries k))) ^ n := by
            rw [coefficientPowerSeries_mem_span_X_pow_iff_coeff_eq_zero]
            intro m hm
            have hcoeff_r :
                PowerSeries.coeff m
                    ((algebraMap ↥A (PowerSeries k)) (r.val n)) =
                  PowerSeries.coeff m
                    (((PowerSeries.trunc n f : Polynomial k) : PowerSeries k)) := by
              change PowerSeries.coeff m ((r.val n : ↥A) : PowerSeries k) =
                PowerSeries.coeff m (((PowerSeries.trunc n f : Polynomial k) : PowerSeries k))
              simp [r, truncA]
            rw [map_sub, hcoeff_r]
            simp [PowerSeries.coeff_trunc, hm]
          simpa [PowerSeries.maximalIdeal_eq_span_X] using hmem_span
      _ = AdicCompletion.evalₐ (maximalIdeal (PowerSeries k)) n
          ((AdicCompletion.ofAlgEquiv (maximalIdeal (PowerSeries k))) f) := by
          simp

-- Proof sketch: `A` is a discrete valuation subring of `k[[x]]` with the same uniformizer `x`,
-- so the maximal-ideal adic topology on `A` is the one induced from the `x`-adic topology on the
-- ambient complete DVR `k[[x]]`; completeness of `k[[x]]` then identifies it with the completion
-- of `A`.
/-- The maximal-ideal adic completion of the coefficient ring `A` is canonically `A`-algebra
isomorphic to `k[[x]]`. -/
noncomputable def finitePthPowerCoefficientSubringCompletionAlgEquivPowerSeries :
    AdicCompletion (maximalIdeal ↥A) ↥A ≃ₐ[↥A]
      PowerSeries k :=
  AlgEquiv.ofBijective (finitePthPowerCoefficientSubringCompletionAlgHom k p)
    (finitePthPowerCoefficientSubringCompletionAlgHom_bijective k p)

/-- The canonical completion comparison sends the image of `a : A` to the same power series in
`k[[x]]`. -/
@[simp]
theorem finitePthPowerCoefficientSubringCompletionAlgEquivPowerSeries_of
    (a : ↥A) :
    finitePthPowerCoefficientSubringCompletionAlgEquivPowerSeries k p
      (AdicCompletion.of (maximalIdeal ↥A) ↥A a) = a := by
  -- The equivalence is built from the raw comparison hom, whose value on dense `A`-points was
  -- isolated above.
  simpa [finitePthPowerCoefficientSubringCompletionAlgEquivPowerSeries,
    AlgEquiv.ofBijective_apply] using
    finitePthPowerCoefficientSubringCompletionAlgHom_of k p a


end SourceFacing
