import Mathlib
import stacks_proof.stacks_project.Chap15.Definition_15_112_1

-- Declarations for this item will be appended below by the statement pipeline.

open IsLocalRing
open IsExtensionOfDiscreteValuationRings

universe u v

section

variable {A : Type u} {B : Type v}
variable [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
variable [CommRing B] [IsDomain B] [IsDiscreteValuationRing B]
variable [Algebra A B] [IsExtensionOfDiscreteValuationRings A B]

attribute [local instance]
  FractionRing.liftAlgebra
  FractionRing.isScalarTower_liftAlgebra

/- Domain-style sampling:
- primary domain: ramification theory for extensions of discrete valuation rings with purely
  inseparable fraction-field extension;
- sampled owner declarations:
  `FractionRing.liftAlgebra`,
  `FractionRing.isScalarTower_liftAlgebra`,
  `IsExtensionOfDiscreteValuationRings.ramificationIndex`,
  `isPurelyInseparable_iff_pow_mem`;
- best owner abstraction: the source-facing owner remains `ramificationIndex A B`, while the
  induced fraction-field algebra `FractionRing A → FractionRing B` and its scalar-tower
  compatibility with `A → B` are canonical derived infrastructure exported by the DVR-extension
  owner rather than installed locally in this file;
- primitive vs. derived: the primitive public data are the DVR extension owner together with the
  characteristic-`p` and purely inseparable hypotheses on the induced fraction-field extension;
  the fraction-field algebra/scalar-tower instances and the `p`-power conclusion are derived API.

Source/core/bridge triage:
- `source-facing`: the conclusion that the ramification index of `A ⊆ B` is a power of `p`;
- `core/canonical`: `IsExtensionOfDiscreteValuationRings.ramificationIndex`,
  `FractionRing.liftAlgebra`, and
  `isPurelyInseparable_iff_pow_mem`;
- `bridge/view`: direct unfolding of `ramificationIndex`, used only to compare the chapter owner
  with the underlying ideal-theoretic invariant.
-/

-- Proof sketch: write a uniformizer of `A` as a unit times a power of a uniformizer of `B`, then
-- use pure inseparability to find a `p`-power of the target uniformizer lying in `FractionRing A`.
-- Comparing valuations gives an equality `k * e = p ^ n` for some `k` and `n`, forcing the
-- ramification index `e` to be a power of `p`.
/-- Helper for Lemma 15.112.4: every discrete valuation ring admits an irreducible generator of its
maximal ideal. -/
lemma exists_uniformizer_generator (R : Type*) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] :
    ∃ π : R, Irreducible π ∧ maximalIdeal R = Ideal.span ({π} : Set R) := by
  -- Choose any irreducible element; in a DVR it is a uniformizer.
  obtain ⟨π, hπirr⟩ := IsDiscreteValuationRing.exists_irreducible R
  refine ⟨π, hπirr, ?_⟩
  exact (IsDiscreteValuationRing.irreducible_iff_uniformizer π).mp hπirr

/-- Helper for Lemma 15.112.4: equality implies association. -/
lemma associated_of_eq {M : Type*} [Monoid M] {x y : M} (hxy : x = y) :
    Associated x y := by
  subst hxy
  exact ⟨1, by simp⟩

/-- Helper for Lemma 15.112.4: associated elements stay associated after applying a monoid map. -/
lemma associated_map {M N : Type*} [CommMonoid M] [CommMonoid N] (f : M →* N) {x y : M}
    (hxy : Associated x y) : Associated (f x) (f y) := by
  rcases hxy with ⟨u, hu⟩
  refine ⟨Units.map f u, ?_⟩
  simpa using congrArg f hu

/-- Helper for Lemma 15.112.4: association is compatible with powers. -/
lemma associated_pow {M : Type*} [CommMonoid M] {x y : M} (hxy : Associated x y) (n : ℕ) :
    Associated (x ^ n) (y ^ n) := by
  rcases hxy with ⟨u, hu⟩
  refine ⟨u ^ n, ?_⟩
  calc
    x ^ n * ↑(u ^ n) = (x * ↑u) ^ n := by
      simp [mul_pow]
    _ = y ^ n := by
      rw [hu]

/-- Helper for Lemma 15.112.4: association is compatible with multiplying by the same factor. -/
lemma associated_mul_right {M : Type*} [CommMonoid M] {x y z : M} (hxy : Associated x y) :
    Associated (x * z) (y * z) := by
  rcases hxy with ⟨u, hu⟩
  refine ⟨u, ?_⟩
  calc
    (x * z) * ↑u = (x * ↑u) * z := by
      ac_rfl
    _ = y * z := by
      rw [hu]

/-- Helper for Lemma 15.112.4: if `x` is associated to `π ^ k`, then `x * π ^ m` is associated to
`π ^ (k + m)`. -/
lemma associated_mul_uniformizer_pow {R : Type*} [CommMonoid R] {π x : R} {k m : ℕ}
    (hx : Associated x (π ^ k)) : Associated (x * π ^ m) (π ^ (k + m)) := by
  -- First push the association across multiplication, then combine the powers.
  refine Associated.trans (associated_mul_right (z := π ^ m) hx) ?_
  exact associated_of_eq (pow_add π k m).symm

/-- Helper for Lemma 15.112.4: a nonzero element of a DVR is associated to a power of any chosen
uniformizer. -/
lemma associated_uniformizer_pow_of_nonzero {R : Type*} [CommRing R] [IsDomain R]
    [IsDiscreteValuationRing R] (π a : R)
    (hπ : maximalIdeal R = Ideal.span ({π} : Set R)) (ha : a ≠ 0) :
    ∃ n : ℕ, Associated a (π ^ n) := by
  -- Classify the principal ideal `(a)` as a power of the maximal ideal.
  have hspan_ne_bot : Ideal.span ({a} : Set R) ≠ ⊥ := by
    simpa [Ideal.span_singleton_eq_bot] using ha
  obtain ⟨n, hn⟩ := exists_maximalIdeal_pow_eq_of_principal R inferInstance
    (Ideal.span ({a} : Set R)) hspan_ne_bot
  refine ⟨n, ?_⟩
  -- Re-express that power through the chosen uniformizer.
  have hspan :
      Ideal.span ({a} : Set R) = Ideal.span ({π ^ n} : Set R) := by
    calc
      Ideal.span ({a} : Set R) = maximalIdeal R ^ n := hn
      _ = (Ideal.span ({π} : Set R)) ^ n := by
        rw [hπ]
      _ = Ideal.span ({π ^ n} : Set R) := by
        simpa using (Ideal.span_singleton_pow π n)
  exact (Ideal.span_singleton_eq_span_singleton).mp hspan

/-- Helper for Lemma 15.112.4: powers of a chosen uniformizer are associated only when their
exponents agree. -/
lemma uniformizer_power_associated_injective {R : Type*} [CommRing R] [IsDomain R]
    [IsDiscreteValuationRing R] (π : R)
    (hπ : maximalIdeal R = Ideal.span ({π} : Set R)) {m n : ℕ}
    (hassoc : Associated (π ^ m) (π ^ n)) : m = n := by
  -- Translate association of powers into equality of maximal-ideal powers.
  have hEq :
      maximalIdeal R ^ m = maximalIdeal R ^ n := by
    calc
      maximalIdeal R ^ m = Ideal.span ({π ^ m} : Set R) := by
        rw [hπ]
        simpa using (Ideal.span_singleton_pow π m)
      _ = Ideal.span ({π ^ n} : Set R) := by
        exact (Ideal.span_singleton_eq_span_singleton).mpr hassoc
      _ = maximalIdeal R ^ n := by
        rw [hπ]
        simpa using (Ideal.span_singleton_pow π n).symm
  by_contra hmn
  have hstrict :
      StrictAnti fun k : ℕ ↦ maximalIdeal R ^ k :=
    Ideal.pow_right_strictAnti (maximalIdeal R) (IsDiscreteValuationRing.not_a_field R)
      (Ideal.IsMaximal.ne_top (IsLocalRing.maximalIdeal.isMaximal R))
  rcases lt_or_gt_of_ne hmn with hlt | hgt
  · exact (hstrict hlt).ne hEq.symm
  · exact (hstrict hgt).ne hEq

/-- Helper for Lemma 15.112.4: pure inseparability puts a `p`-power of a chosen target
uniformizer inside the image of the base fraction field. -/
lemma exists_fraction_power_of_uniformizer_in_base
    (p : ℕ) [Fact p.Prime] [CharP (FractionRing A) p]
    [IsPurelyInseparable (FractionRing A) (FractionRing B)]
    (πB : B) :
    ∃ n : ℕ, ∃ x : FractionRing A,
      algebraMap (FractionRing A) (FractionRing B) x =
        algebraMap B (FractionRing B) πB ^ (p ^ n) := by
  -- Apply the standard pointwise characterization of pure inseparability.
  have hpure :
      ∀ y : FractionRing B,
        ∃ n : ℕ, y ^ p ^ n ∈ (algebraMap (FractionRing A) (FractionRing B)).range := by
    exact
      (isPurelyInseparable_iff_pow_mem (F := FractionRing A) (E := FractionRing B) p).mp
        (show IsPurelyInseparable (FractionRing A) (FractionRing B) from inferInstance)
  obtain ⟨n, x, hx⟩ := hpure (algebraMap B (FractionRing B) πB)
  refine ⟨n, x, ?_⟩
  simpa [RingHom.map_pow] using hx

/-- Helper for Lemma 15.112.4: the image of a chosen source uniformizer is associated to the
corresponding ramification-index power of a chosen target uniformizer. -/
lemma uniformizer_image_associated_uniformizer_pow_ramificationIndex
    (πA : A) (πB : B)
    (hπA : maximalIdeal A = Ideal.span ({πA} : Set A))
    (hπB : maximalIdeal B = Ideal.span ({πB} : Set B)) :
    Associated (algebraMap A B πA) (πB ^ ramificationIndex A B) := by
  -- Rewrite the defining ideal equality for the ramification index through the chosen generators.
  have hram :
      Ideal.map (algebraMap A B) (maximalIdeal A) = maximalIdeal B ^ ramificationIndex A B :=
    (ramificationIndex_eq_iff (A := A) (B := B) (ramificationIndex A B)).mp rfl |>.2
  have hspan :
      Ideal.span ({algebraMap A B πA} : Set B) = Ideal.span ({πB ^ ramificationIndex A B} : Set B) := by
    calc
      Ideal.span ({algebraMap A B πA} : Set B)
          = Ideal.map (algebraMap A B) (Ideal.span ({πA} : Set A)) := by
            rw [Ideal.map_span]
            ext y
            simp
      _ = Ideal.map (algebraMap A B) (maximalIdeal A) := by
        rw [hπA]
      _ = maximalIdeal B ^ ramificationIndex A B := hram
      _ = (Ideal.span ({πB} : Set B)) ^ ramificationIndex A B := by
        rw [hπB]
      _ = Ideal.span ({πB ^ ramificationIndex A B} : Set B) := by
        simpa using (Ideal.span_singleton_pow πB (ramificationIndex A B))
  exact (Ideal.span_singleton_eq_span_singleton).mp hspan

/-- Helper for Lemma 15.112.4: after mapping a nonzero base element into `B`, its chosen
uniformizer exponent gets multiplied by the ramification index. -/
lemma algebraMap_associated_uniformizer_pow
    (πA : A) (πB : B)
    (hπA : maximalIdeal A = Ideal.span ({πA} : Set A))
    (hπB : maximalIdeal B = Ideal.span ({πB} : Set B))
    {a : A} (ha : a ≠ 0) :
    ∃ n : ℕ, Associated (algebraMap A B a) (πB ^ (ramificationIndex A B * n)) := by
  -- First decompose `a` with respect to the source uniformizer.
  obtain ⟨n, hassocA⟩ := associated_uniformizer_pow_of_nonzero πA a hπA ha
  refine ⟨n, ?_⟩
  have hmapA : Associated (algebraMap A B a) ((algebraMap A B πA) ^ n) := by
    simpa [RingHom.map_pow] using associated_map (algebraMap A B).toMonoidHom hassocA
  have hmapπ : Associated ((algebraMap A B πA) ^ n) ((πB ^ ramificationIndex A B) ^ n) := by
    exact associated_pow
      (uniformizer_image_associated_uniformizer_pow_ramificationIndex πA πB hπA hπB) n
  have hpow :
      Associated ((πB ^ ramificationIndex A B) ^ n) (πB ^ (ramificationIndex A B * n)) := by
    exact associated_of_eq (pow_mul πB (ramificationIndex A B) n).symm
  exact Associated.trans hmapA (Associated.trans hmapπ hpow)

/-- Helper for Lemma 15.112.4: if a mapped base element becomes a pure target-uniformizer power,
then the exponent is divisible by the ramification index. -/
lemma ramificationIndex_dvd_exponent_of_base_element_eq_uniformizer_power
    (πA : A) (πB : B)
    (hπA : maximalIdeal A = Ideal.span ({πA} : Set A))
    (hπB : maximalIdeal B = Ideal.span ({πB} : Set B))
    {a s : A} {m : ℕ}
    (hs : s ≠ 0)
    (ha : a ≠ 0)
    (hEq : algebraMap A B a = algebraMap A B s * πB ^ m) :
    ramificationIndex A B ∣ m := by
  -- Compare the uniformizer exponents on both sides of the equality in `B`.
  obtain ⟨na, hna⟩ := algebraMap_associated_uniformizer_pow πA πB hπA hπB ha
  obtain ⟨ns, hns⟩ := algebraMap_associated_uniformizer_pow πA πB hπA hπB hs
  have hEqAssoc : Associated (algebraMap A B a) (algebraMap A B s * πB ^ m) :=
    associated_of_eq hEq
  have hright :
      Associated (algebraMap A B s * πB ^ m) (πB ^ (ramificationIndex A B * ns + m)) :=
    associated_mul_uniformizer_pow hns
  have hpow :
      Associated (πB ^ (ramificationIndex A B * na)) (πB ^ (ramificationIndex A B * ns + m)) := by
    exact Associated.trans (Associated.symm hna) (Associated.trans hEqAssoc hright)
  have hexp :
      ramificationIndex A B * na = ramificationIndex A B * ns + m :=
    uniformizer_power_associated_injective πB hπB hpow
  have hdivSum : ramificationIndex A B ∣ ramificationIndex A B * ns + m := by
    rw [← hexp]
    exact dvd_mul_of_dvd_left (dvd_refl (ramificationIndex A B)) na
  have hdivBase : ramificationIndex A B ∣ ramificationIndex A B * ns :=
    dvd_mul_of_dvd_left (dvd_refl (ramificationIndex A B)) ns
  -- Subtract the known multiple to isolate the remaining exponent `m`.
  have hdivSub :
      ramificationIndex A B ∣
        (ramificationIndex A B * ns + m) - ramificationIndex A B * ns :=
    Nat.dvd_sub hdivSum hdivBase
  simpa using hdivSub

/-- Helper for Lemma 15.112.4: if a target-uniformizer power comes from the base fraction field,
then its exponent is divisible by the ramification index. -/
lemma ramificationIndex_dvd_exponent_of_base_fraction_eq_uniformizer_power
    (πA : A) (πB : B)
    (hπA : maximalIdeal A = Ideal.span ({πA} : Set A))
    (hπB : maximalIdeal B = Ideal.span ({πB} : Set B))
    {m : ℕ} {x : FractionRing A}
    (hx : algebraMap (FractionRing A) (FractionRing B) x =
      algebraMap B (FractionRing B) πB ^ m) :
    ramificationIndex A B ∣ m := by
  -- Write `x` as a fraction `a / s` and clear the denominator in `B`.
  obtain ⟨⟨a, s⟩, hsx⟩ := IsLocalization.surj (nonZeroDivisors A) x
  have hs0 : (s : A) ≠ 0 := by
    exact (mem_nonZeroDivisors_iff_ne_zero).mp s.2
  have hs_map :
      algebraMap B (FractionRing B) (algebraMap A B (s : A)) =
        algebraMap (FractionRing A) (FractionRing B) (algebraMap A (FractionRing A) (s : A)) := by
    calc
      algebraMap B (FractionRing B) (algebraMap A B (s : A)) =
          algebraMap A (FractionRing B) (s : A) := by
        simpa [RingHom.comp_apply] using
          (DFunLike.congr_fun (IsScalarTower.algebraMap_eq A B (FractionRing B)) (s : A)).symm
      _ = algebraMap (FractionRing A) (FractionRing B)
            (algebraMap A (FractionRing A) (s : A)) := by
        simpa [RingHom.comp_apply] using
          DFunLike.congr_fun (IsScalarTower.algebraMap_eq A (FractionRing A) (FractionRing B))
            (s : A)
  have ha_map :
      algebraMap B (FractionRing B) (algebraMap A B a) =
        algebraMap (FractionRing A) (FractionRing B) (algebraMap A (FractionRing A) a) := by
    calc
      algebraMap B (FractionRing B) (algebraMap A B a) = algebraMap A (FractionRing B) a := by
        simpa [RingHom.comp_apply] using
          (DFunLike.congr_fun (IsScalarTower.algebraMap_eq A B (FractionRing B)) a).symm
      _ = algebraMap (FractionRing A) (FractionRing B) (algebraMap A (FractionRing A) a) := by
        simpa [RingHom.comp_apply] using
          DFunLike.congr_fun (IsScalarTower.algebraMap_eq A (FractionRing A) (FractionRing B)) a
  have hEqFrac :
      algebraMap B (FractionRing B) (algebraMap A B s * πB ^ m) =
        algebraMap B (FractionRing B) (algebraMap A B a) := by
    calc
      algebraMap B (FractionRing B) (algebraMap A B (s : A) * πB ^ m)
          = algebraMap B (FractionRing B) (algebraMap A B (s : A)) *
              algebraMap B (FractionRing B) πB ^ m := by
                simp
      _ = algebraMap (FractionRing A) (FractionRing B)
            (algebraMap A (FractionRing A) (s : A)) *
            algebraMap (FractionRing A) (FractionRing B) x := by
              rw [hs_map, ← hx]
      _ = algebraMap (FractionRing A) (FractionRing B)
            (algebraMap A (FractionRing A) (s : A) * x) := by
              simp
      _ = algebraMap (FractionRing A) (FractionRing B)
            (x * algebraMap A (FractionRing A) (s : A)) := by
              rw [mul_comm]
      _ = algebraMap (FractionRing A) (FractionRing B) (algebraMap A (FractionRing A) a) := by
              rw [hsx]
      _ = algebraMap B (FractionRing B) (algebraMap A B a) := by
              rw [ha_map]
  have hEqB :
      algebraMap A B (s : A) * πB ^ m = algebraMap A B a := by
    exact IsFractionRing.injective B (FractionRing B) hEqFrac
  have hExt : IsExtensionOfDiscreteValuationRings A B := inferInstance
  have hsB0 : algebraMap A B s ≠ 0 := by
    exact (map_ne_zero_iff (algebraMap A B) hExt.algebraMap_injective).2 hs0
  have hpow0 : πB ^ m ≠ 0 := by
    exact pow_ne_zero m (by
      have hπBirr : Irreducible πB := (IsDiscreteValuationRing.irreducible_iff_uniformizer πB).mpr hπB
      exact hπBirr.ne_zero)
  have ha0 : a ≠ 0 := by
    refine (map_ne_zero_iff (algebraMap A B) hExt.algebraMap_injective).1 ?_
    rw [← hEqB]
    exact mul_ne_zero hsB0 hpow0
  exact ramificationIndex_dvd_exponent_of_base_element_eq_uniformizer_power
    πA πB hπA hπB hs0 ha0 hEqB.symm

/-- Helper for Lemma 15.112.4: every divisor of a prime power is itself a prime power. -/
lemma eq_pow_of_dvd_prime_pow (p : ℕ) [Fact p.Prime] {m n : ℕ} (hm : m ∣ p ^ n) :
    ∃ t : ℕ, m = p ^ t := by
  obtain ⟨t, -, ht⟩ := (Nat.dvd_prime_pow Fact.out).mp hm
  exact ⟨t, ht⟩

/-- Lemma 15.112.4: if `A ⊆ B` is an extension of discrete valuation rings, the induced extension
of fraction fields `FractionRing A ⊆ FractionRing B` has characteristic `p > 0`, and
`FractionRing B` is purely inseparable over `FractionRing A`, then the ramification index of
`A ⊆ B` is a power of `p`. -/
@[stacks 09E6]
theorem ramificationIndex_eq_pow_of_isPurelyInseparable
    (p : ℕ) [Fact p.Prime] [CharP (FractionRing A) p]
    [IsPurelyInseparable (FractionRing A) (FractionRing B)] :
    ∃ n : ℕ,
      ramificationIndex A B = p ^ n := by
  -- Choose generators of the two maximal ideals.
  obtain ⟨πA, hπAirr, hπA⟩ := exists_uniformizer_generator A
  obtain ⟨πB, -, hπB⟩ := exists_uniformizer_generator B
  -- Pure inseparability produces a `p`-power of `πB` coming from the base fraction field.
  obtain ⟨n, x, hx⟩ := exists_fraction_power_of_uniformizer_in_base (A := A) (B := B) p πB
  -- Comparing uniformizer exponents shows that the ramification index divides that `p`-power.
  have hdiv : ramificationIndex A B ∣ p ^ n :=
    ramificationIndex_dvd_exponent_of_base_fraction_eq_uniformizer_power
      πA πB hπA hπB hx
  -- A divisor of a prime power is again a prime power.
  obtain ⟨t, ht⟩ := eq_pow_of_dvd_prime_pow p hdiv
  refine ⟨t, ?_⟩
  exact ht

end
