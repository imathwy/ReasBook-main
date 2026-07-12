import Mathlib.RingTheory.PowerSeries.Ideal
import Mathlib.RingTheory.PowerSeries.Trunc
import Mathlib.RingTheory.LaurentSeries
import Mathlib.RingTheory.Valuation.LocalSubring
import Mathlib.Tactic.Recall
import StacksProject_2024.Chap10.Definition_10_37_1
import StacksProject_2024.Chap10.Lemma_10_37_4
import Mathlib.Tactic.StacksAttribute

-- Declarations for this item will be appended below by the statement pipeline.

open scoped PowerSeries

universe u

variable {R : Type u} [CommRing R]

section

variable [IsNoetherianRing R]

/- Lemma 10.37.9 (Noetherian part): if `R` is a Noetherian normal domain, then `R⟦X⟧` is
Noetherian. This is exactly the canonical mathlib instance on `R⟦X⟧`; the textbook's normality
assumptions are stronger than needed for this part. -/
recall PowerSeries.instIsNoetherianRing

end

section

variable [IsDomain R] [IsNoetherianRing R] [IsIntegrallyClosed R]

/-- Helper for Chap10 Lemma 10 37 9: map a power series over `R` to a Laurent series over the
fraction field of `R` by mapping coefficients and then viewing the result as a Laurent series. -/
noncomputable def powerSeriesToLaurent :
    R⟦X⟧ →+* LaurentSeries (FractionRing R) :=
  (algebraMap (FractionRing R)⟦X⟧ (LaurentSeries (FractionRing R))).comp
    (algebraMap R⟦X⟧ (FractionRing R)⟦X⟧)

omit [IsNoetherianRing R] [IsIntegrallyClosed R] in
/-- Helper for Chap10 Lemma 10 37 9: the coefficientwise Laurent-series embedding of `R⟦X⟧` is
injective. -/
lemma powerSeriesToLaurent_injective :
    Function.Injective (powerSeriesToLaurent (R := R)) := by
  intro f g hfg
  have hmap :
      algebraMap R⟦X⟧ (FractionRing R)⟦X⟧ f =
        algebraMap R⟦X⟧ (FractionRing R)⟦X⟧ g := by
    exact IsFractionRing.injective (PowerSeries (FractionRing R))
      (LaurentSeries (FractionRing R)) hfg
  exact
    (PowerSeries.map_injective (algebraMap R (FractionRing R))
      (IsFractionRing.injective R (FractionRing R))) <|
      by simpa [powerSeriesToLaurent, PowerSeries.algebraMap_apply''] using hmap

omit [IsDomain R] [IsNoetherianRing R] [IsIntegrallyClosed R] in
/-- Helper for Chap10 Lemma 10 37 9: coefficients of the Laurent image are the fraction-field
images of the original coefficients, and negative coefficients vanish. -/
lemma coeff_powerSeriesToLaurent (f : R⟦X⟧) (z : ℤ) :
    (powerSeriesToLaurent (R := R) f).coeff z =
      if z < 0 then 0
      else algebraMap R (FractionRing R) (PowerSeries.coeff z.natAbs f) := by
  -- Expand the bridge map once, then use the standard Laurent-series coefficient formula.
  simp [powerSeriesToLaurent, LaurentSeries.coe_algebraMap, PowerSeries.algebraMap_apply'',
    PowerSeries.coeff_map, PowerSeries.coeff_coe]

omit [IsNoetherianRing R] [IsIntegrallyClosed R] in
/-- Helper for Chap10 Lemma 10 37 9: a nonzero power series stays nonzero after passage to
Laurent series. -/
lemma powerSeriesToLaurent_ne_zero {f : R⟦X⟧} (hf : f ≠ 0) :
    powerSeriesToLaurent (R := R) f ≠ 0 := by
  intro hzero
  apply hf
  exact powerSeriesToLaurent_injective (R := R) (by simpa using hzero)

omit [IsNoetherianRing R] [IsIntegrallyClosed R] in
/-- Helper for Chap10 Lemma 10 37 9: the Laurent-series image of a nonzero power series has the
same order as the original power series. -/
lemma order_powerSeriesToLaurent {h : R⟦X⟧} (hh : h ≠ 0) :
    (powerSeriesToLaurent (R := R) h).order = h.order.toNat := by
  let m := h.order.toNat
  have hne : powerSeriesToLaurent (R := R) h ≠ 0 := powerSeriesToLaurent_ne_zero (R := R) hh
  have hcoeff_ne : (powerSeriesToLaurent (R := R) h).coeff (m : ℤ) ≠ 0 := by
    simpa [m, coeff_powerSeriesToLaurent, PowerSeries.coeff_order hh]
  have hle : (powerSeriesToLaurent (R := R) h).order ≤ m :=
    HahnSeries.order_le_of_coeff_ne_zero hcoeff_ne
  have hge : (m : ℤ) ≤ (powerSeriesToLaurent (R := R) h).order := by
    refine (HahnSeries.le_order_iff_forall (x := powerSeriesToLaurent (R := R) h) hne).2 ?_
    intro j hj
    by_cases hjneg : j < 0
    · simpa [coeff_powerSeriesToLaurent, hjneg]
    · have hjnonneg : 0 ≤ j := le_of_not_gt hjneg
      have hjnat : j.natAbs < m := by
        lift j to ℕ using hjnonneg with jnat
        exact_mod_cast hj
      simpa [coeff_powerSeriesToLaurent, hjneg, Int.natAbs_of_nonneg hjnonneg, m,
        PowerSeries.coeff_of_lt_order_toNat _ hjnat]
  exact le_antisymm hle hge

/-- Helper for Chap10 Lemma 10 37 9: extend the coefficientwise Laurent-series map from
`R⟦X⟧` to its fraction field. -/
noncomputable def fracToLaurent :
    FractionRing (R⟦X⟧) →+* LaurentSeries (FractionRing R) :=
  IsFractionRing.lift (powerSeriesToLaurent_injective (R := R))

omit [IsNoetherianRing R] [IsIntegrallyClosed R] in
/-- Helper for Chap10 Lemma 10 37 9: the Laurent-series transport on the fraction field is
injective. -/
lemma fracToLaurent_injective :
    Function.Injective (fracToLaurent (R := R)) := by
  exact RingHom.injective (fracToLaurent (R := R))

omit [IsNoetherianRing R] [IsIntegrallyClosed R] in
/-- Helper for Chap10 Lemma 10 37 9: the fraction-field Laurent bridge extends the original
coefficientwise Laurent embedding on `R⟦X⟧`. -/
lemma fracToLaurent_algebraMap (f : R⟦X⟧) :
    fracToLaurent (R := R) (algebraMap R⟦X⟧ (FractionRing (R⟦X⟧)) f) =
      powerSeriesToLaurent (R := R) f := by
  -- Unfold only the fraction-field lift, then use its canonical computation rule.
  simpa [fracToLaurent] using
    (IsFractionRing.lift_algebraMap (A := R⟦X⟧) (K := FractionRing (R⟦X⟧))
      (L := LaurentSeries (FractionRing R)) (g := powerSeriesToLaurent (R := R))
      (powerSeriesToLaurent_injective (R := R)) f)

omit [IsNoetherianRing R] [IsIntegrallyClosed R] in
/-- Helper for Chap10 Lemma 10 37 9: an integral fraction-field element admits the textbook
almost-integral witness after transport to Laurent series. -/
lemma laurentWitnessOfIsIntegral {x : FractionRing (R⟦X⟧)}
    (hx : IsIntegral R⟦X⟧ x) :
    ∃ h : R⟦X⟧, h ≠ 0 ∧ ∀ e : ℕ, ∃ g : R⟦X⟧,
      powerSeriesToLaurent (R := R) h * fracToLaurent (R := R) x ^ e =
        powerSeriesToLaurent (R := R) g := by
  obtain ⟨h, hh, hpow⟩ := hx.isAlmostIntegral
  refine ⟨h, mem_nonZeroDivisors_iff_ne_zero.mp hh, ?_⟩
  intro e
  rcases hpow e with ⟨g, hg⟩
  have hmap_h :
      fracToLaurent (R := R) (algebraMap R⟦X⟧ (FractionRing (R⟦X⟧)) h) =
        powerSeriesToLaurent (R := R) h := by
    exact fracToLaurent_algebraMap (R := R) h
  have hmap_g :
      fracToLaurent (R := R) (algebraMap R⟦X⟧ (FractionRing (R⟦X⟧)) g) =
        powerSeriesToLaurent (R := R) g := by
    exact fracToLaurent_algebraMap (R := R) g
  refine ⟨g, ?_⟩
  -- Route correction: map the almost-integral witness itself, not a new integrality statement.
  calc
    powerSeriesToLaurent (R := R) h * fracToLaurent (R := R) x ^ e =
        fracToLaurent (R := R) (algebraMap R⟦X⟧ (FractionRing (R⟦X⟧)) h * x ^ e) := by
          rw [← hmap_h, ← map_pow, ← map_mul]
    _ = fracToLaurent (R := R) (algebraMap R⟦X⟧ (FractionRing (R⟦X⟧)) g) := by
          simpa [Algebra.smul_def] using congrArg (fracToLaurent (R := R)) hg.symm
    _ = powerSeriesToLaurent (R := R) g := by
          exact hmap_g

omit [IsNoetherianRing R] [IsIntegrallyClosed R] in
/-- Helper for Chap10 Lemma 10 37 9: if one fixed nonzero power series clears every power of a
Laurent series back into the power-series image, then the Laurent series has nonnegative order. -/
lemma orderNonneg_ofMulPow_memImage {w : LaurentSeries (FractionRing R)} {h : R⟦X⟧}
    (hh : h ≠ 0)
    (hw : ∀ e : ℕ, ∃ g : R⟦X⟧,
      powerSeriesToLaurent (R := R) h * w ^ e = powerSeriesToLaurent (R := R) g) :
    0 ≤ w.order := by
  by_cases hwzero : w = 0
  · simpa [hwzero, HahnSeries.order_zero]
  · by_contra hnonneg
    have hneg : w.order < 0 := lt_of_not_ge hnonneg
    let m := h.order.toNat
    let e : ℕ := m + 1
    rcases hw e with ⟨g, hg⟩
    have hhLaurent : powerSeriesToLaurent (R := R) h ≠ 0 :=
      powerSeriesToLaurent_ne_zero (R := R) hh
    have hpow_ne : w ^ e ≠ 0 := pow_ne_zero e hwzero
    have hprod_ne : powerSeriesToLaurent (R := R) h * w ^ e ≠ 0 := by
      exact mul_ne_zero hhLaurent hpow_ne
    have hprod_order :
        (powerSeriesToLaurent (R := R) h * w ^ e).order = (m : ℤ) + e * w.order := by
      rw [HahnSeries.order_mul hhLaurent hpow_ne, order_powerSeriesToLaurent (R := R) hh,
        HahnSeries.order_pow]
      simpa [m, e]
    have hprod_neg :
        (powerSeriesToLaurent (R := R) h * w ^ e).order < 0 := by
      have hwle : w.order ≤ -1 := by
        omega
      have he_nonneg : 0 ≤ (e : ℤ) := by
        omega
      have hmul :
          (e : ℤ) * w.order ≤ (e : ℤ) * (-1 : ℤ) := by
        gcongr
      have hsum : (m : ℤ) + (e : ℤ) * w.order ≤ -1 := by
        calc
          (m : ℤ) + (e : ℤ) * w.order ≤ (m : ℤ) + (e : ℤ) * (-1 : ℤ) := by
            gcongr
          _ = -1 := by
            simp [e]
      rw [hprod_order]
      omega
    have hcoeff_ne :
        (powerSeriesToLaurent (R := R) h * w ^ e).coeff
            ((powerSeriesToLaurent (R := R) h * w ^ e).order) ≠ 0 := by
      intro hzero
      exact hprod_ne (HahnSeries.coeff_order_eq_zero.mp hzero)
    have hcoeff_zero :
        (powerSeriesToLaurent (R := R) h * w ^ e).coeff
            ((powerSeriesToLaurent (R := R) h * w ^ e).order) = 0 := by
      rw [hg]
      have hgneg : (powerSeriesToLaurent (R := R) g).order < 0 := by
        simpa [hg] using hprod_neg
      simpa [coeff_powerSeriesToLaurent, hgneg]
    exact hcoeff_ne hcoeff_zero

omit [IsDomain R] [IsNoetherianRing R] [IsIntegrallyClosed R] in
/-- Helper for Chap10 Lemma 10 37 9: taking the coefficient at the order of a witness isolates
the constant coefficient of the second factor. -/
lemma coeffOrder_mul_eq {K : Type*} [Field K] [Algebra R K] {h : R⟦X⟧}
    (g : K⟦X⟧) :
    PowerSeries.coeff h.order.toNat ((algebraMap R⟦X⟧ K⟦X⟧ h) * g) =
      algebraMap R K (PowerSeries.coeff h.order.toNat h) * g.constantCoeff := by
  classical
  -- Only the order term of the nonzero witness can contribute to this coefficient.
  rw [PowerSeries.coeff_mul]
  calc
    ∑ p ∈ Finset.antidiagonal h.order.toNat,
        PowerSeries.coeff p.1 ((algebraMap R⟦X⟧ K⟦X⟧) h) * PowerSeries.coeff p.2 g =
          PowerSeries.coeff h.order.toNat ((algebraMap R⟦X⟧ K⟦X⟧) h) * PowerSeries.coeff 0 g := by
            rw [Finset.sum_eq_single_of_mem (h.order.toNat, 0)]
            · simp
            · intro ij hij hneq
              rcases ij with ⟨i, j⟩
              rw [Finset.mem_antidiagonal] at hij
              have hi_lt : i < h.order.toNat := by
                have hi_ne : i ≠ h.order.toNat := by
                  intro hi_eq
                  apply hneq
                  ext
                  · simpa [hi_eq]
                  · simpa [hi_eq] using hij
                lia
              have hcoeff_zero :
                  PowerSeries.coeff i ((algebraMap R⟦X⟧ K⟦X⟧) h) = 0 := by
                simp [PowerSeries.algebraMap_apply'', PowerSeries.coeff_map,
                  PowerSeries.coeff_of_lt_order_toNat i hi_lt]
              rw [hcoeff_zero, zero_mul]
    _ = algebraMap R K (PowerSeries.coeff h.order.toNat h) * g.constantCoeff := by
          simp [PowerSeries.algebraMap_apply'', PowerSeries.coeff_map]

/-- Helper for Chap10 Lemma 10 37 9: if the coefficients below `n` vanish, then the series is
`X^n` times its shifted tail. -/
lemma eq_X_pow_mul_shift_of_vanishingBelow {K : Type*} [Field K] {f : K⟦X⟧} {n : ℕ}
    (hvan : ∀ i < n, PowerSeries.coeff i f = 0) :
    f = PowerSeries.X ^ n * PowerSeries.mk (fun i ↦ PowerSeries.coeff (i + n) f) := by
  -- The truncation vanishes because every coefficient below `n` is zero.
  have htrunc : PowerSeries.trunc n f = 0 := by
    ext i
    rw [Polynomial.coeff_zero, PowerSeries.coeff_trunc]
    split_ifs with hi
    · exact hvan i hi
    · rfl
  simpa [htrunc] using (PowerSeries.eq_X_pow_mul_shift_add_trunc n f)

/-- Helper for Chap10 Lemma 10 37 9: a coefficient becomes `R`-valued once all earlier
coefficients vanish and one has an almost-integral witness coming from `R⟦X⟧`. -/
lemma coeff_eq_algebraMap_of_mul_pow_mem_range_of_vanishingBelow
    {K : Type*} [Field K] [Algebra R K] [IsFractionRing R K] {y : K⟦X⟧} {n : ℕ}
    (h : R⟦X⟧) (hh : h ≠ 0)
    (hw : ∀ e : ℕ, ∃ g : R⟦X⟧,
      (algebraMap R⟦X⟧ K⟦X⟧ h) * y ^ e = algebraMap R⟦X⟧ K⟦X⟧ g)
    (hvan : ∀ i < n, PowerSeries.coeff i y = 0) :
    ∃ r : R, algebraMap R K r = PowerSeries.coeff n y := by
  let m := h.order.toNat
  let b : R := PowerSeries.coeff m h
  have hb : b ≠ 0 := by
    simpa [m, b] using PowerSeries.coeff_order hh
  let u : K⟦X⟧ := PowerSeries.mk fun i ↦ PowerSeries.coeff (i + n) y
  have hy_shift : y = PowerSeries.X ^ n * u := by
    simpa [u] using eq_X_pow_mul_shift_of_vanishingBelow (K := K) hvan
  have hu_const : u.constantCoeff = PowerSeries.coeff n y := by
    simp [u]
  have hcoeffmul (e : ℕ) :
      PowerSeries.coeff (m + e * n) ((algebraMap R⟦X⟧ K⟦X⟧ h) * y ^ e) =
        algebraMap R K b * (PowerSeries.coeff n y) ^ e := by
    -- First strip off the common factor `X^(e * n)` coming from the vanishing initial segment.
    calc
      PowerSeries.coeff (m + e * n) ((algebraMap R⟦X⟧ K⟦X⟧ h) * y ^ e) =
          PowerSeries.coeff (m + e * n)
            ((algebraMap R⟦X⟧ K⟦X⟧ h) * ((PowerSeries.X ^ n) ^ e * u ^ e)) := by
              rw [hy_shift, mul_pow]
      _ = PowerSeries.coeff (m + e * n)
            (((algebraMap R⟦X⟧ K⟦X⟧ h) * u ^ e) * PowerSeries.X ^ (e * n)) := by
              rw [← pow_mul]
              simp [mul_left_comm, mul_comm]
      _ = PowerSeries.coeff m ((algebraMap R⟦X⟧ K⟦X⟧ h) * u ^ e) := by
            rw [PowerSeries.coeff_mul_X_pow']
            simp [m]
      _ = algebraMap R K b * (u ^ e).constantCoeff := by
            simpa [m, b] using coeffOrder_mul_eq (K := K) (u ^ e)
      _ = algebraMap R K b * (PowerSeries.coeff n y) ^ e := by
            rw [map_pow, hu_const]
  have halmost : IsAlmostIntegral R (PowerSeries.coeff n y) := by
    -- The first nonzero coefficient of the witness controls every power of the target coefficient.
    refine ⟨b, mem_nonZeroDivisors_iff_ne_zero.mpr hb, fun e ↦ ?_⟩
    rcases hw e with ⟨g, hg⟩
    refine ⟨PowerSeries.coeff (m + e * n) g, ?_⟩
    calc
      algebraMap R K (PowerSeries.coeff (m + e * n) g) =
          PowerSeries.coeff (m + e * n) (algebraMap R⟦X⟧ K⟦X⟧ g) := by
            simp [PowerSeries.algebraMap_apply'', PowerSeries.coeff_map]
      _ = PowerSeries.coeff (m + e * n) ((algebraMap R⟦X⟧ K⟦X⟧ h) * y ^ e) := by
            rw [← hg]
      _ = algebraMap R K b * (PowerSeries.coeff n y) ^ e := hcoeffmul e
      _ = b • (PowerSeries.coeff n y) ^ e := by
            simp [Algebra.smul_def]
  -- Noetherianity upgrades almost integrality to integrality, and integrally closedness finishes.
  have hy_int : IsIntegral R (PowerSeries.coeff n y) :=
    IsAlmostIntegral.isIntegral halmost
  exact IsIntegrallyClosed.algebraMap_eq_of_integral hy_int

/- Layer triage for Lemma 10.37.9:
- the Noetherian statement above is a `core/canonical` recall from mathlib;
- the normal statement below is still `source-facing`, but its owner abstraction is the chapter
  notion `IsIntegrallyClosed` on the power series ring.

The primitive data are exactly the domain, Noetherian, and integrally closed hypotheses on `R`;
normality of `R⟦X⟧` is derived API. -/
/- Lemma 10.37.9 (normal part): if `R` is a Noetherian normal domain, then `R⟦X⟧` is normal.
By Definition 10.37.1, the canonical formulation of this part is the typeclass fact
`IsIntegrallyClosed R⟦X⟧`. -/
/-- Helper for Chap10 Lemma 10 37 9: if an integral fraction-field element has Laurent
coefficients below `n` equal to zero, then its `n`th Laurent coefficient comes from `R`. -/
lemma coeff_eq_algebraMap_of_isIntegral_of_vanishingBelow
    {x : FractionRing (R⟦X⟧)} {n : ℕ}
    (hx : IsIntegral R⟦X⟧ x)
    (hvan : ∀ i < n, (fracToLaurent (R := R) x).coeff i = 0) :
    ∃ r : R, algebraMap R (FractionRing R) r = (fracToLaurent (R := R) x).coeff n := by
  let w : LaurentSeries (FractionRing R) := fracToLaurent (R := R) x
  obtain ⟨h, hh, hw⟩ := laurentWitnessOfIsIntegral (R := R) hx
  have horder : 0 ≤ w.order := by
    exact orderNonneg_ofMulPow_memImage (R := R) hh (by simpa [w] using hw)
  let y : (FractionRing R)⟦X⟧ := PowerSeries.X ^ Int.natAbs w.order * w.powerSeriesPart
  have hy : ((y : (FractionRing R)⟦X⟧) : LaurentSeries (FractionRing R)) = w := by
    -- Convert the Laurent tail to a genuine power series exactly once.
    dsimp [y]
    exact LaurentSeries.X_order_mul_powerSeriesPart (f := w) (by
      simpa using Int.natAbs_of_nonneg horder)
  have hwPower :
      ∀ e : ℕ, ∃ g : R⟦X⟧,
        (algebraMap R⟦X⟧ (FractionRing R)⟦X⟧ h) * y ^ e =
          algebraMap R⟦X⟧ (FractionRing R)⟦X⟧ g := by
    intro e
    rcases hw e with ⟨g, hg⟩
    refine ⟨g, ?_⟩
    apply IsFractionRing.injective (PowerSeries (FractionRing R))
      (LaurentSeries (FractionRing R))
    -- Transport the Laurent witness equation back through the power-series embedding.
    calc
      (((algebraMap R⟦X⟧ (FractionRing R)⟦X⟧ h) * y ^ e : (FractionRing R)⟦X⟧) :
          LaurentSeries (FractionRing R)) =
          (powerSeriesToLaurent (R := R) h) * (((y : (FractionRing R)⟦X⟧) :
            LaurentSeries (FractionRing R))) ^ e := by
              simp [powerSeriesToLaurent]
      _ = powerSeriesToLaurent (R := R) h * w ^ e := by rw [hy]
      _ = powerSeriesToLaurent (R := R) g := hg
      _ = (((algebraMap R⟦X⟧ (FractionRing R)⟦X⟧ g : (FractionRing R)⟦X⟧) :
            LaurentSeries (FractionRing R))) := by
              simp [powerSeriesToLaurent]
  have hyvan : ∀ i < n, PowerSeries.coeff i y = 0 := by
    intro i hi
    have hcoeff : PowerSeries.coeff i y = w.coeff i := by
      simpa using congrArg (fun z : LaurentSeries (FractionRing R) => z.coeff i) hy
    rw [hcoeff, hvan i hi]
  rcases coeff_eq_algebraMap_of_mul_pow_mem_range_of_vanishingBelow
      (R := R) (K := FractionRing R) h hh hwPower hyvan with ⟨r, hr⟩
  have hcoeffn : PowerSeries.coeff n y = w.coeff n := by
    simpa using congrArg (fun z : LaurentSeries (FractionRing R) => z.coeff n) hy
  refine ⟨r, ?_⟩
  simpa [w, hcoeffn] using hr

/-- Helper for Chap10 Lemma 10 37 9: every nonnegative Laurent coefficient of an integral
fraction-field element already lies in the base ring `R`. -/
lemma coeffsInBaseRing_ofIsIntegral {x : FractionRing (R⟦X⟧)}
    (hx : IsIntegral R⟦X⟧ x) :
    ∀ n : ℕ, ∃ r : R, algebraMap R (FractionRing R) r = (fracToLaurent (R := R) x).coeff n := by
  classical
  intro n
  refine Nat.strong_induction_on n ?_
  intro n ih
  let a : (i : ℕ) → i < n → R := fun i hi ↦ Classical.choose (ih i hi)
  let initialSegment : R⟦X⟧ := PowerSeries.mk (fun i ↦ if hi : i < n then a i hi else 0)
  let xTail : FractionRing (R⟦X⟧) :=
    x - algebraMap R⟦X⟧ (FractionRing (R⟦X⟧)) initialSegment
  have hxTail : IsIntegral R⟦X⟧ xTail := by
    -- Subtract the already constructed finite prefix and keep integrality.
    simpa [xTail] using hx.sub (isIntegral_algebraMap (x := initialSegment))
  have hmap_prefix :
      fracToLaurent (R := R) (algebraMap R⟦X⟧ (FractionRing (R⟦X⟧)) initialSegment) =
        powerSeriesToLaurent (R := R) initialSegment := by
    exact fracToLaurent_algebraMap (R := R) initialSegment
  have htail :
      fracToLaurent (R := R) xTail =
        fracToLaurent (R := R) x - powerSeriesToLaurent (R := R) initialSegment := by
    simp [xTail, hmap_prefix]
  have htailvan : ∀ i < n, (fracToLaurent (R := R) xTail).coeff i = 0 := by
    intro i hi
    have hai : algebraMap R (FractionRing R) (a i hi) =
        (fracToLaurent (R := R) x).coeff i := by
      exact Classical.choose_spec (ih i hi)
    -- The prefix removes exactly the already known initial coefficients.
    rw [htail, HahnSeries.coeff_sub, coeff_powerSeriesToLaurent]
    rw [if_neg (not_lt_of_ge (Int.natCast_nonneg i))]
    simp [initialSegment, hi, hai]
  rcases coeff_eq_algebraMap_of_isIntegral_of_vanishingBelow
      (R := R) hxTail htailvan with ⟨r, hr⟩
  have hprefix_n :
      (powerSeriesToLaurent (R := R) initialSegment).coeff n = 0 := by
    rw [coeff_powerSeriesToLaurent]
    simp [initialSegment]
  have htail_n :
      (fracToLaurent (R := R) xTail).coeff n = (fracToLaurent (R := R) x).coeff n := by
    rw [htail, HahnSeries.coeff_sub, hprefix_n, sub_zero]
  refine ⟨r, ?_⟩
  simpa [htail_n] using hr

/-- Helper for Chap10 Lemma 10 37 9: an integral fraction-field element is represented by a
power series over `R`. -/
lemma exists_powerSeries_eq_of_isIntegral {x : FractionRing (R⟦X⟧)}
    (hx : IsIntegral R⟦X⟧ x) :
    ∃ f : R⟦X⟧, algebraMap R⟦X⟧ (FractionRing (R⟦X⟧)) f = x := by
  classical
  let w : LaurentSeries (FractionRing R) := fracToLaurent (R := R) x
  have hcoeff : ∀ n : ℕ, ∃ r : R, algebraMap R (FractionRing R) r = w.coeff n := by
    simpa [w] using coeffsInBaseRing_ofIsIntegral (R := R) hx
  choose a ha using hcoeff
  let f : R⟦X⟧ := PowerSeries.mk a
  obtain ⟨h, hh, hw⟩ := laurentWitnessOfIsIntegral (R := R) hx
  have horder : 0 ≤ w.order := by
    exact orderNonneg_ofMulPow_memImage (R := R) hh (by simpa [w] using hw)
  have hseries : powerSeriesToLaurent (R := R) f = w := by
    -- Match Laurent coefficients separately in negative and nonnegative degrees.
    ext z
    by_cases hz : z < 0
    · rw [coeff_powerSeriesToLaurent, if_pos hz]
      exact (HahnSeries.coeff_eq_zero_of_lt_order
        (show z < w.order from lt_of_lt_of_le hz horder)).symm
    · have hznonneg : 0 ≤ z := le_of_not_gt hz
      lift z to ℕ using hznonneg with n
      rw [coeff_powerSeriesToLaurent, if_neg (Int.natCast_nonneg n).not_gt]
      simpa [f, ha n]
  refine ⟨f, ?_⟩
  apply fracToLaurent_injective (R := R)
  -- Injectivity of the Laurent bridge descends the reconstructed equality to the fraction field.
  calc
    fracToLaurent (R := R) (algebraMap R⟦X⟧ (FractionRing (R⟦X⟧)) f) =
        powerSeriesToLaurent (R := R) f := by
          exact fracToLaurent_algebraMap (R := R) f
    _ = w := hseries
    _ = fracToLaurent (R := R) x := rfl

-- Proof sketch: write an integral element of the fraction field of `R⟦X⟧` as a Laurent
-- series, use almost integrality over the coefficient ring to show its lowest coefficient lies in
-- `R`, and iterate on higher coefficients to prove every coefficient lies in `R`.
/-- Chap10 Lemma 10 37 9: if `R` is a Noetherian normal domain, then `R⟦X⟧` is integrally
closed. -/
@[stacks 0BI0]
instance instIsIntegrallyClosedPowerSeries : IsIntegrallyClosed R⟦X⟧ := by
  -- Route correction: finish the textbook Laurent-series argument through coefficient induction
  -- and then descend the reconstructed power series through the injective bridge `fracToLaurent`.
  rw [isIntegrallyClosed_iff (K := FractionRing (R⟦X⟧))]
  intro x hx
  exact exists_powerSeries_eq_of_isIntegral (R := R) hx

end
