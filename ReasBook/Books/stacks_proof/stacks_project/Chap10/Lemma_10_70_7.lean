import StacksProject_2024.Chap10.Lemma_10_70_2
import Mathlib.Tactic.StacksAttribute

-- Declarations for this item will be appended below by the statement pipeline.

open PrimeSpectrum
open scoped nonZeroDivisors

universe u

section

variable {R : Type u} [CommRing R]

private theorem affineBlowupChart_span_singleton_radical_eq_of_zeroLocus_eq
    (I : Ideal R) (f : R)
    (hV : zeroLocus ({f} : Set R) = zeroLocus (I : Set R)) :
    (Ideal.span ({f} : Set R)).radical = I.radical := by
  rw [← zeroLocus_eq_iff, zeroLocus_span]
  exact hV

/-- Helper for Lemma 10.70.7: in the affine blowup chart, a radical equality
`√(f) = √I` forces a power of the chart parameter to be divisible by the image of `f`. -/
private theorem affineBlowupChart_parameter_pow_eq_image_mul_of_radical_eq
    (I : Ideal R) (a : I) (f : R)
    (hI : (Ideal.span ({f} : Set R)).radical = I.radical) :
    ∃ n : ℕ, ∃ b : affineBlowupChart I a,
      (algebraMap R (affineBlowupChart I a) a.1) ^ n =
        algebraMap R (affineBlowupChart I a) f * b := by
  let A := affineBlowupChart I a
  let aA : A := algebraMap R A a.1
  let fA : A := algebraMap R A f
  -- The source radical equality puts `a` in the radical of `(f)`.
  have ha_rad : a.1 ∈ (Ideal.span ({f} : Set R)).radical := by
    rw [hI]
    exact Ideal.le_radical a.2
  obtain ⟨n, hn⟩ := Ideal.mem_radical_iff.mp ha_rad
  obtain ⟨r, hr⟩ := Ideal.mem_span_singleton'.mp hn
  refine ⟨n, algebraMap R A r, ?_⟩
  -- Mapping the source divisibility relation into the chart gives the required factorization.
  calc
    aA ^ n = algebraMap R A (a.1 ^ n) := by simp [aA]
    _ = algebraMap R A (r * f) := by rw [hr.symm]
    _ = algebraMap R A r * fA := by simp [fA]
    _ = fA * algebraMap R A r := by rw [mul_comm]

/-- Helper for Lemma 10.70.7: in the affine blowup chart, a radical equality
`√(f) = √I` forces a power of the image of `f` to be divisible by the chart parameter. -/
private theorem affineBlowupChart_image_pow_eq_parameter_mul_of_radical_eq
    (I : Ideal R) (a : I) (f : R)
    (hI : (Ideal.span ({f} : Set R)).radical = I.radical) :
    ∃ m : ℕ, ∃ c : affineBlowupChart I a,
      (algebraMap R (affineBlowupChart I a) f) ^ m =
        algebraMap R (affineBlowupChart I a) a.1 * c := by
  let A := affineBlowupChart I a
  let aA : A := algebraMap R A a.1
  let fA : A := algebraMap R A f
  have hmapI : Ideal.map (algebraMap R A) I = Ideal.span {aA} := by
    simpa [A, aA] using affineBlowupChart_map_ideal_eq_span_singleton I a
  -- The generator `f` of `(f)` already lies in `√I`, so some power lands in `I`.
  have hf_rad : f ∈ I.radical := by
    rw [← hI]
    exact Ideal.le_radical (Ideal.subset_span (by simp))
  obtain ⟨m, hm⟩ := Ideal.mem_radical_iff.mp hf_rad
  have hmA : algebraMap R A (f ^ m) ∈ Ideal.map (algebraMap R A) I :=
    Ideal.mem_map_of_mem (algebraMap R A) hm
  rw [hmapI, Ideal.mem_span_singleton'] at hmA
  obtain ⟨c, hc⟩ := hmA
  refine ⟨m, c, ?_⟩
  -- Rewriting the mapped membership in the principal ideal gives the reciprocal factorization.
  calc
    fA ^ m = algebraMap R A (f ^ m) := by simp [fA]
    _ = c * aA := hc.symm
    _ = aA * c := by rw [mul_comm]

/-- Helper for Lemma 10.70.7: mutual power divisibility between `a` and `f` lets an
`a`-localization be viewed as an `f`-localization. -/
private theorem isLocalizationAway_of_pow_factorizations
    {A S : Type*} [CommRing A] [CommRing S] [Algebra A S]
    (a f : A) [IsLocalization.Away a S]
    (ha : ∃ n : ℕ, ∃ b : A, a ^ n = f * b)
    (hf : ∃ m : ℕ, ∃ c : A, f ^ m = a * c) :
    IsLocalization.Away f S := by
  obtain ⟨n, b, hb⟩ := ha
  obtain ⟨m, c, hc⟩ := hf
  refine IsLocalization.Away.mk f ?_ ?_ ?_
  · -- The first factorization shows that the image of `f` divides a unit.
    have hdiv : f ∣ a ^ n := ⟨b, hb⟩
    have ha_unit : IsUnit (algebraMap A S (a ^ n)) := by
      simpa [map_pow] using ((IsLocalization.Away.algebraMap_isUnit a).pow n)
    exact isUnit_of_dvd_unit
      (map_dvd (algebraMap A S) hdiv)
      ha_unit
  · intro z
    -- Start from the standard `a`-localization normal form and replace powers of `a`.
    obtain ⟨k, d, hk⟩ := IsLocalization.Away.surj a z
    have hpow : f ^ (m * k) = a ^ k * c ^ k := by
      rw [pow_mul, hc, mul_pow]
    have hpowS : algebraMap A S f ^ (m * k) =
        algebraMap A S a ^ k * algebraMap A S c ^ k := by
      simpa [map_pow, map_mul] using congrArg (fun x : A => algebraMap A S x) hpow
    refine ⟨m * k, d * c ^ k, ?_⟩
    calc
      z * algebraMap A S f ^ (m * k) = z * (algebraMap A S a ^ k * algebraMap A S c ^ k) := by
        rw [hpowS]
      _ = (z * algebraMap A S a ^ k) * algebraMap A S c ^ k := by
        rw [mul_assoc]
      _ = algebraMap A S d * algebraMap A S c ^ k := by rw [hk]
      _ = algebraMap A S (d * c ^ k) := by
        simp [map_mul, map_pow]
  · intro x y hxy
    -- Equality in the `a`-localization is cleared by a power of `a`, hence by a power of `f`.
    obtain ⟨k, hk⟩ := IsLocalization.Away.exists_of_eq (S := S) a hxy
    have hpow : f ^ (m * k) = a ^ k * c ^ k := by
      rw [pow_mul, hc, mul_pow]
    refine ⟨m * k, ?_⟩
    calc
      f ^ (m * k) * x = (a ^ k * c ^ k) * x := by rw [hpow]
      _ = c ^ k * (a ^ k * x) := by simp [mul_assoc, mul_comm]
      _ = c ^ k * (a ^ k * y) := by rw [hk]
      _ = (a ^ k * c ^ k) * y := by simp [mul_assoc, mul_comm]
      _ = f ^ (m * k) * y := by rw [hpow]

/-- Lemma 10.70.7 in canonical algebraic form: if the principal ideal `(f)` and `I` have the same
radical, then the image of `f` in `R[I/a]` is a nonzerodivisor. -/
@[stacks 080U]
theorem affineBlowupChart_isRegular_of_radical_eq
    (I : Ideal R) (a : I) (f : R)
    (hI : (Ideal.span ({f} : Set R)).radical = I.radical) :
    IsRegular (algebraMap R (affineBlowupChart I a) f) := by
  -- The source proof first shows that a power of `a` is a multiple of the image of `f`.
  obtain ⟨n, b, hb⟩ := affineBlowupChart_parameter_pow_eq_image_mul_of_radical_eq I a f hI
  have hreg_a :
      IsRegular (algebraMap R (affineBlowupChart I a) a.1) :=
    affineBlowupChart_isRegular I a
  have hreg_pow :
      IsRegular ((algebraMap R (affineBlowupChart I a) a.1) ^ n) :=
    hreg_a.pow n
  -- Since `a^n = f * b` and `a^n` is regular, the factor `f` is regular as well.
  rw [hb] at hreg_pow
  exact (isRegular_mul_iff.mp hreg_pow).1

/-- Lemma 10.70.7 in canonical algebraic form: if the principal ideal `(f)` and `I` have the same
radical, then `R_a` is the localization of `R[I/a]` away from the image of `f`. -/
@[stacks 080U]
theorem affineBlowupChart_isLocalizationAway_of_radical_eq
    (I : Ideal R) (a : I) (f : R)
    (hI : (Ideal.span ({f} : Set R)).radical = I.radical) :
    IsLocalization.Away (algebraMap R (affineBlowupChart I a) f) (Localization.Away a.1) := by
  let A := affineBlowupChart I a
  let aA : A := algebraMap R A a.1
  let fA : A := algebraMap R A f
  have hfa : ∃ n : ℕ, ∃ b : A, aA ^ n = fA * b := by
    simpa [A, aA, fA] using affineBlowupChart_parameter_pow_eq_image_mul_of_radical_eq I a f hI
  have haf : ∃ m : ℕ, ∃ c : A, fA ^ m = aA * c := by
    simpa [A, aA, fA] using affineBlowupChart_image_pow_eq_parameter_mul_of_radical_eq I a f hI
  -- The two transported factorizations let us reuse the standard `a`-localization structure.
  exact isLocalizationAway_of_pow_factorizations aA fA hfa haf

/-- Lemma 10.70.7 in the source-text form `V(f) = V(I)`: the image of `f` in `R[I/a]` is a
nonzerodivisor. -/
@[stacks 080U]
theorem affineBlowupChart_isRegular_of_zeroLocus_eq
    (I : Ideal R) (a : I) (f : R)
    (hV : zeroLocus ({f} : Set R) = zeroLocus (I : Set R)) :
    IsRegular (algebraMap R (affineBlowupChart I a) f) :=
  affineBlowupChart_isRegular_of_radical_eq I a f
    (affineBlowupChart_span_singleton_radical_eq_of_zeroLocus_eq I f hV)

/-- Lemma 10.70.7 in the source-text form `V(f) = V(I)`: `R_a` is the localization of `R[I/a]`
away from the image of `f`. -/
@[stacks 080U]
theorem affineBlowupChart_isLocalizationAway_of_zeroLocus_eq
    (I : Ideal R) (a : I) (f : R)
    (hV : zeroLocus ({f} : Set R) = zeroLocus (I : Set R)) :
    IsLocalization.Away (algebraMap R (affineBlowupChart I a) f) (Localization.Away a.1) :=
  affineBlowupChart_isLocalizationAway_of_radical_eq I a f
    (affineBlowupChart_span_singleton_radical_eq_of_zeroLocus_eq I f hV)

end
