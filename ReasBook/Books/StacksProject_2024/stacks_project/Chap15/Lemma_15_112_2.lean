import Mathlib.Algebra.Order.Hom.Units
import Mathlib.NumberTheory.RamificationInertia.Basic
import Mathlib.Tactic.Recall
import Mathlib.RingTheory.Valuation.Discrete.Basic
import StacksProject_2024.stacks_project.Chap15.Definition_15_112_1
import StacksProject_2024.stacks_project.Chap15.Lemma_15_124_2

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

open Ideal IsLocalRing

/- Domain-style sampling for Lemma 15.112.2:
- primary domain: ramification and inertia for extensions of discrete valuation rings with finite
  fraction-field extension;
- sampled owner declarations:
  `IsExtensionOfDiscreteValuationRings.residueDegree`,
  `IsExtensionOfDiscreteValuationRings.residueDegree_eq_finrank`,
  `finiteDimensional_residueField_of_finiteDimensional_fractionField_extension`,
  `ramificationIndex_mul_residueDegree_le_finrank_of_finiteDimensional_fractionField_extension`;
- best owner abstraction: the source-facing DVR extension owner is
  `IsExtensionOfDiscreteValuationRings`, while the core numerical statements are the valuation-ring
  extension theorems from `Lemma_15_124_2`;
- primitive-vs-derived split: the primitive data for the source-facing lemma are the DVR extension
  together with the finite-dimensional fraction-field hypothesis, while the owner-level comparison
  `valuationRing_ramificationIndex_le` is the remaining bridge from the chapter's DVR
  ramification index to the valuation-ring quotient cardinal; the chapter names
  `ramificationIndex` and `residueDegree` are the source-facing DVR owners reused directly in the
  bridge statements below.

Source/core/bridge triage:
- `source-facing`: the textbook statements in terms of `ramificationIndex A B` and
  `residueDegree A B`;
- `core/canonical`: the valuation-ring extension theorems
  `finiteDimensional_residueField_of_finiteDimensional_fractionField_extension` and
  `ramificationIndex_mul_residueDegree_le_finrank_of_finiteDimensional_fractionField_extension`;
- `bridge/view`: the specialization of those valuation-ring theorems to the chapter-local DVR
  owner.
-/

section

variable {A : Type u} {B : Type v}
variable [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
variable [CommRing B] [IsDomain B] [IsDiscreteValuationRing B]
variable [Algebra A B] [IsExtensionOfDiscreteValuationRings A B]

attribute [local instance]
  FractionRing.liftAlgebra
  FractionRing.isScalarTower_liftAlgebra

/- Lemma 15.112.2 (1): for an extension of discrete valuation rings `A ⊂ B`, if the induced
fraction-field extension `FractionRing B / FractionRing A` is finite, then the induced residue
field extension is finite. This is the exact valuation-ring owner theorem recalled in the
discrete-valuation-ring setting via the canonical instance
`discreteValuationRingExtension_toIsExtensionOfValuationRings`. -/
recall finiteDimensional_residueField_of_finiteDimensional_fractionField_extension

attribute [local instance]
  finiteDimensional_residueField_of_finiteDimensional_fractionField_extension

namespace IsExtensionOfDiscreteValuationRings

local notation "K[" A "]" => FractionRing A
local notation "Γ[" B "]" => ValuativeRel.ValueGroupWithZero K[B]
local notation "Q" =>
  Γ[B]ˣ ⧸ MonoidWithZeroHom.valueGroup (ValuativeExtension.mapValueGroupWithZero K[A] K[B])

/-- Helper for Lemma 15.112.2: the finite-dimensional fraction-field hypothesis induces the
finite-dimensional residue-field hypothesis needed to interpret `residueDegree A B`. -/
lemma finiteDimensional_residueField_instance
    [FiniteDimensional (FractionRing A) (FractionRing B)] :
    FiniteDimensional (ResidueField A) (ResidueField B) :=
  finiteDimensional_residueField_of_finiteDimensional_fractionField_extension

attribute [local instance] finiteDimensional_residueField_instance

/-- Helper for Lemma 15.112.2: every discrete valuation ring admits a chosen generator of its
maximal ideal. -/
lemma exists_uniformizer_generator (R : Type*)
    [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] :
    ∃ π : R, Irreducible π ∧ maximalIdeal R = Ideal.span ({π} : Set R) := by
  -- Choose an irreducible element and read it as a uniformizer.
  obtain ⟨π, hπirr⟩ := IsDiscreteValuationRing.exists_irreducible R
  refine ⟨π, hπirr, ?_⟩
  exact (IsDiscreteValuationRing.irreducible_iff_uniformizer π).mp hπirr

/-- Helper for Lemma 15.112.2: equality gives an association relation. -/
lemma associated_of_eq {M : Type*} [Monoid M] {x y : M} (hxy : x = y) :
    Associated x y := by
  -- Rewriting reduces the goal to the trivial unit witness.
  subst hxy
  exact ⟨1, by simp⟩

/-- Helper for Lemma 15.112.2: association is preserved by a monoid homomorphism. -/
lemma associated_map {M N : Type*} [CommMonoid M] [CommMonoid N] (f : M →* N) {x y : M}
    (hxy : Associated x y) :
    Associated (f x) (f y) := by
  -- Push the associating unit through the map.
  rcases hxy with ⟨u, hu⟩
  refine ⟨Units.map f u, ?_⟩
  simpa using congrArg f hu

/-- Helper for Lemma 15.112.2: association is compatible with powers. -/
lemma associated_pow {M : Type*} [CommMonoid M] {x y : M}
    (hxy : Associated x y) (n : ℕ) :
    Associated (x ^ n) (y ^ n) := by
  -- Raise the associating unit to the same power.
  rcases hxy with ⟨u, hu⟩
  refine ⟨u ^ n, ?_⟩
  calc
    x ^ n * ↑(u ^ n) = (x * ↑u) ^ n := by simp [mul_pow]
    _ = y ^ n := by rw [hu]

/-- Helper for Lemma 15.112.2: association is stable under multiplying both sides by the same
factor. -/
lemma associated_mul_right {M : Type*} [CommMonoid M] {x y z : M}
    (hxy : Associated x y) :
    Associated (x * z) (y * z) := by
  -- Keep the same unit witness and reassociate the products.
  rcases hxy with ⟨u, hu⟩
  refine ⟨u, ?_⟩
  calc
    (x * z) * ↑u = (x * ↑u) * z := by ac_rfl
    _ = y * z := by rw [hu]

/-- Helper for Lemma 15.112.2: if `x` is associated to `π ^ k`, then multiplying by `π ^ m`
shifts the exponent by `m`. -/
lemma associated_mul_uniformizer_pow {R : Type*} [CommMonoid R] {π x : R} {k m : ℕ}
    (hx : Associated x (π ^ k)) :
    Associated (x * π ^ m) (π ^ (k + m)) := by
  -- First append the common factor, then merge the two powers of the uniformizer.
  refine Associated.trans (associated_mul_right (z := π ^ m) hx) ?_
  exact associated_of_eq (pow_add π k m).symm

/-- Helper for Lemma 15.112.2: multiplying on the left by a unit preserves the associated class.
-/
lemma associated_of_unit_mul_left {M : Type*} [CommMonoid M] (u : Units M) (x : M) :
    Associated ((u : M) * x) x := by
  -- The inverse unit exhibits the new product as another representative of the same class.
  refine ⟨u⁻¹, ?_⟩
  simpa [mul_assoc] using show ((u : M) * x) * (u⁻¹ : Units M) = x by
    calc
      ((u : M) * x) * (u⁻¹ : Units M) = x * ((u : M) * (u⁻¹ : Units M)) := by ac_rfl
      _ = x := by simp

/-- Helper for Lemma 15.112.2: a nonzero element of a DVR is associated to a power of a chosen
uniformizer. -/
lemma associated_uniformizer_pow_of_nonzero {R : Type*} [CommRing R] [IsDomain R]
    [IsDiscreteValuationRing R] (π a : R)
    (hπ : maximalIdeal R = Ideal.span ({π} : Set R)) (ha : a ≠ 0) :
    ∃ n : ℕ, Associated a (π ^ n) := by
  -- First classify the principal ideal `(a)` as a power of the maximal ideal.
  have hspan_ne_bot : Ideal.span ({a} : Set R) ≠ ⊥ := by
    simpa [Ideal.span_singleton_eq_bot] using ha
  obtain ⟨n, hn⟩ := exists_maximalIdeal_pow_eq_of_principal R inferInstance
    (Ideal.span ({a} : Set R)) hspan_ne_bot
  refine ⟨n, ?_⟩
  -- Then rewrite that power through the chosen generator `π`.
  have hspan :
      Ideal.span ({a} : Set R) = Ideal.span ({π ^ n} : Set R) := by
    calc
      Ideal.span ({a} : Set R) = maximalIdeal R ^ n := hn
      _ = (Ideal.span ({π} : Set R)) ^ n := by rw [hπ]
      _ = Ideal.span ({π ^ n} : Set R) := by
          simpa using (Ideal.span_singleton_pow π n)
  exact (Ideal.span_singleton_eq_span_singleton).mp hspan

/-- Helper for Lemma 15.112.2: powers of a chosen uniformizer are associated only when their
exponents agree. -/
lemma uniformizer_power_associated_injective {R : Type*} [CommRing R] [IsDomain R]
    [IsDiscreteValuationRing R] (π : R)
    (hπ : maximalIdeal R = Ideal.span ({π} : Set R)) {m n : ℕ}
    (hassoc : Associated (π ^ m) (π ^ n)) :
    m = n := by
  -- Translate the association into equality of the corresponding maximal-ideal powers.
  have hEq : maximalIdeal R ^ m = maximalIdeal R ^ n := by
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

/-- Helper for Lemma 15.112.2: the mapped maximal ideal of the source DVR is the
`ramificationIndex A B`-th power of the target maximal ideal. -/
lemma mapped_maximalIdeal_eq_pow_ramificationIndex :
    (maximalIdeal A).map (algebraMap A B) = maximalIdeal B ^ ramificationIndex A B := by
  -- Read the ideal identity directly from the defining characterization of the DVR ramification
  -- index.
  simpa using
    (ramificationIndex_eq_iff A B (ramificationIndex A B)).mp rfl |>.2

/-- Helper for Lemma 15.112.2: the image of a chosen source uniformizer is associated to the
`ramificationIndex A B`-th power of a chosen target uniformizer. -/
lemma uniformizer_image_associated_uniformizer_pow_ramificationIndex
    (πA : A) (πB : B)
    (hπA : maximalIdeal A = Ideal.span ({πA} : Set A))
    (hπB : maximalIdeal B = Ideal.span ({πB} : Set B)) :
    Associated (algebraMap A B πA) (πB ^ ramificationIndex A B) := by
  -- Rewrite the ramification-index ideal identity through the chosen generators.
  have hspan :
      Ideal.span ({algebraMap A B πA} : Set B) =
        Ideal.span ({πB ^ ramificationIndex A B} : Set B) := by
    calc
      Ideal.span ({algebraMap A B πA} : Set B) =
          Ideal.map (algebraMap A B) (Ideal.span ({πA} : Set A)) := by
            rw [Ideal.map_span]
            ext y
            simp
      _ = Ideal.map (algebraMap A B) (maximalIdeal A) := by rw [hπA]
      _ = maximalIdeal B ^ ramificationIndex A B :=
            mapped_maximalIdeal_eq_pow_ramificationIndex (A := A) (B := B)
      _ = (Ideal.span ({πB} : Set B)) ^ ramificationIndex A B := by rw [hπB]
      _ = Ideal.span ({πB ^ ramificationIndex A B} : Set B) := by
            simpa using (Ideal.span_singleton_pow πB (ramificationIndex A B))
  exact (Ideal.span_singleton_eq_span_singleton).mp hspan

/-- Helper for Lemma 15.112.2: mapping a nonzero base element to `B` multiplies its chosen
uniformizer exponent by the ramification index. -/
lemma algebraMap_associated_uniformizer_pow
    (πA : A) (πB : B)
    (hπA : maximalIdeal A = Ideal.span ({πA} : Set A))
    (hπB : maximalIdeal B = Ideal.span ({πB} : Set B))
    {a : A} (ha : a ≠ 0) :
    ∃ n : ℕ, Associated (algebraMap A B a) (πB ^ (ramificationIndex A B * n)) := by
  -- Decompose the source element into a uniformizer power and map that decomposition to `B`.
  obtain ⟨n, hassocA⟩ := associated_uniformizer_pow_of_nonzero πA a hπA ha
  refine ⟨n, ?_⟩
  have hmapA : Associated (algebraMap A B a) ((algebraMap A B πA) ^ n) := by
    simpa [RingHom.map_pow] using associated_map (algebraMap A B).toMonoidHom hassocA
  have hmapπ :
      Associated ((algebraMap A B πA) ^ n) ((πB ^ ramificationIndex A B) ^ n) := by
    exact associated_pow
      (uniformizer_image_associated_uniformizer_pow_ramificationIndex
        (A := A) (B := B) πA πB hπA hπB) n
  have hpow :
      Associated ((πB ^ ramificationIndex A B) ^ n) (πB ^ (ramificationIndex A B * n)) := by
    exact associated_of_eq (pow_mul πB (ramificationIndex A B) n).symm
  exact Associated.trans hmapA (Associated.trans hmapπ hpow)

/-- Helper for Lemma 15.112.2: if a mapped base element becomes a pure target-uniformizer power,
then the exponent is divisible by the ramification index. -/
lemma ramificationIndex_dvd_exponent_of_base_element_eq_uniformizer_power
    (πA : A) (πB : B)
    (hπA : maximalIdeal A = Ideal.span ({πA} : Set A))
    (hπB : maximalIdeal B = Ideal.span ({πB} : Set B))
    {a s : A} {m : ℕ}
    (hs : s ≠ 0) (ha : a ≠ 0)
    (hEq : algebraMap A B a = algebraMap A B s * πB ^ m) :
    ramificationIndex A B ∣ m := by
  -- Express both source elements with target-side uniformizer exponents and compare them.
  obtain ⟨na, hna⟩ := algebraMap_associated_uniformizer_pow πA πB hπA hπB ha
  obtain ⟨ns, hns⟩ := algebraMap_associated_uniformizer_pow πA πB hπA hπB hs
  have hEqAssoc : Associated (algebraMap A B a) (algebraMap A B s * πB ^ m) :=
    associated_of_eq hEq
  have hright :
      Associated (algebraMap A B s * πB ^ m)
        (πB ^ (ramificationIndex A B * ns + m)) := by
    exact associated_mul_uniformizer_pow hns
  have hpow :
      Associated (πB ^ (ramificationIndex A B * na))
        (πB ^ (ramificationIndex A B * ns + m)) := by
    exact Associated.trans (Associated.symm hna) (Associated.trans hEqAssoc hright)
  have hexp :
      ramificationIndex A B * na = ramificationIndex A B * ns + m :=
    uniformizer_power_associated_injective πB hπB hpow
  have hdivSum : ramificationIndex A B ∣ ramificationIndex A B * ns + m := by
    rw [← hexp]
    exact dvd_mul_of_dvd_left (dvd_refl (ramificationIndex A B)) na
  have hdivBase : ramificationIndex A B ∣ ramificationIndex A B * ns :=
    dvd_mul_of_dvd_left (dvd_refl (ramificationIndex A B)) ns
  -- Subtract the known multiple to isolate the remaining exponent.
  have hdivSub :
      ramificationIndex A B ∣
        (ramificationIndex A B * ns + m) - ramificationIndex A B * ns :=
    Nat.dvd_sub hdivSum hdivBase
  simpa using hdivSub

/-- Helper for Lemma 15.112.2: if a target-uniformizer power comes from the base fraction field,
then its exponent is divisible by the ramification index. -/
lemma ramificationIndex_dvd_exponent_of_base_fraction_eq_uniformizer_power
    (πA : A) (πB : B)
    (hπA : maximalIdeal A = Ideal.span ({πA} : Set A))
    (hπB : maximalIdeal B = Ideal.span ({πB} : Set B))
    {m : ℕ} {x : FractionRing A}
    (hx : algebraMap (FractionRing A) (FractionRing B) x =
      algebraMap B (FractionRing B) πB ^ m) :
    ramificationIndex A B ∣ m := by
  -- Write the source fraction as `a / s` and clear denominators inside `B`.
  obtain ⟨⟨a, s⟩, hsx⟩ := IsLocalization.surj (nonZeroDivisors A) x
  have hs0 : (s : A) ≠ 0 := by
    exact (mem_nonZeroDivisors_iff_ne_zero).mp s.2
  have hs_map :
      algebraMap B (FractionRing B) (algebraMap A B (s : A)) =
        algebraMap (FractionRing A) (FractionRing B) (algebraMap A (FractionRing A) (s : A)) := by
    -- Compare the two scalar-tower routes for the denominator.
    calc
      algebraMap B (FractionRing B) (algebraMap A B (s : A)) =
          algebraMap A (FractionRing B) (s : A) := by
            simpa [RingHom.comp_apply] using
              (DFunLike.congr_fun (IsScalarTower.algebraMap_eq A B (FractionRing B)) (s : A)).symm
      _ =
          algebraMap (FractionRing A) (FractionRing B) (algebraMap A (FractionRing A) (s : A)) := by
            simpa [RingHom.comp_apply] using
              DFunLike.congr_fun
                (IsScalarTower.algebraMap_eq A (FractionRing A) (FractionRing B)) (s : A)
  have ha_map :
      algebraMap B (FractionRing B) (algebraMap A B a) =
        algebraMap (FractionRing A) (FractionRing B) (algebraMap A (FractionRing A) a) := by
    -- The numerator follows the same scalar-tower comparison.
    calc
      algebraMap B (FractionRing B) (algebraMap A B a) =
          algebraMap A (FractionRing B) a := by
            simpa [RingHom.comp_apply] using
              (DFunLike.congr_fun (IsScalarTower.algebraMap_eq A B (FractionRing B)) a).symm
      _ =
          algebraMap (FractionRing A) (FractionRing B) (algebraMap A (FractionRing A) a) := by
            simpa [RingHom.comp_apply] using
              DFunLike.congr_fun
                (IsScalarTower.algebraMap_eq A (FractionRing A) (FractionRing B)) a
  have hEqFrac :
      algebraMap B (FractionRing B) (algebraMap A B s * πB ^ m) =
        algebraMap B (FractionRing B) (algebraMap A B a) := by
    -- Clearing denominators in the fraction field produces an equality in `FractionRing B`.
    calc
      algebraMap B (FractionRing B) (algebraMap A B (s : A) * πB ^ m) =
          algebraMap B (FractionRing B) (algebraMap A B (s : A)) *
            algebraMap B (FractionRing B) πB ^ m := by
              simp
      _ =
          algebraMap (FractionRing A) (FractionRing B)
            (algebraMap A (FractionRing A) (s : A)) *
            algebraMap (FractionRing A) (FractionRing B) x := by
              rw [hs_map, ← hx]
      _ =
          algebraMap (FractionRing A) (FractionRing B)
            (algebraMap A (FractionRing A) (s : A) * x) := by
              simp
      _ =
          algebraMap (FractionRing A) (FractionRing B)
            (x * algebraMap A (FractionRing A) (s : A)) := by rw [mul_comm]
      _ =
          algebraMap (FractionRing A) (FractionRing B) (algebraMap A (FractionRing A) a) := by
            rw [hsx]
      _ = algebraMap B (FractionRing B) (algebraMap A B a) := by rw [ha_map]
  have hEqB :
      algebraMap A B (s : A) * πB ^ m = algebraMap A B a := by
    -- Injectivity of the fraction-field map brings the equality back down to `B`.
    exact IsFractionRing.injective B (FractionRing B) hEqFrac
  have hExt : IsExtensionOfDiscreteValuationRings A B := inferInstance
  have hsB0 : algebraMap A B s ≠ 0 := by
    exact (map_ne_zero_iff (algebraMap A B) hExt.algebraMap_injective).2 hs0
  have hpow0 : πB ^ m ≠ 0 := by
    exact pow_ne_zero m (by
      have hπBirr : Irreducible πB :=
        (IsDiscreteValuationRing.irreducible_iff_uniformizer πB).mpr hπB
      exact hπBirr.ne_zero)
  have ha0 : a ≠ 0 := by
    refine (map_ne_zero_iff (algebraMap A B) hExt.algebraMap_injective).1 ?_
    rw [← hEqB]
    exact mul_ne_zero hsB0 hpow0
  exact ramificationIndex_dvd_exponent_of_base_element_eq_uniformizer_power
    πA πB hπA hπB hs0 ha0 hEqB.symm

/-- Helper for Lemma 15.112.2: a chosen target uniformizer has nonzero image in the target
fraction field, so every power defines a fraction-field unit. -/
lemma uniformizer_power_fraction_ne_zero
    (πB : B) (hπB : maximalIdeal B = Ideal.span ({πB} : Set B)) (k : ℕ) :
    algebraMap B K[B] πB ^ k ≠ 0 := by
  -- Uniformizers are irreducible and hence nonzero, and field maps preserve nonzeroness.
  have hπBirr : Irreducible πB :=
    (IsDiscreteValuationRing.irreducible_iff_uniformizer πB).mpr hπB
  exact pow_ne_zero k (by
    exact map_ne_zero_iff (algebraMap B K[B]) (IsFractionRing.injective B K[B]) |>.2 hπBirr.ne_zero)

/-- Helper for Lemma 15.112.2: the image of a chosen target-uniformizer power in the fraction
field defines a canonical unit. -/
noncomputable def uniformizer_power_fraction_unit
    (πB : B) (hπB : maximalIdeal B = Ideal.span ({πB} : Set B)) (k : ℕ) : K[B]ˣ :=
  Units.mk0 (algebraMap B K[B] πB ^ k)
    (uniformizer_power_fraction_ne_zero (B := B) πB hπB k)

/-- Helper for Lemma 15.112.2: an element of the subgroup generated by the source value monoid is
already the image of a source value-group unit. -/
lemma exists_source_value_group_unit_of_mem_valueGroup
    {γ : Γ[B]ˣ}
    (hγ : γ ∈ MonoidWithZeroHom.valueGroup
      (ValuativeExtension.mapValueGroupWithZero K[A] K[B])) :
    ∃ δ : Γ[A]ˣ,
      Units.map (ValuativeExtension.mapValueGroupWithZero K[A] K[B]).toMonoidHom δ = γ := by
  let H : Subgroup Γ[B]ˣ :=
    (Units.map (ValuativeExtension.mapValueGroupWithZero K[A] K[B]).toMonoidHom).range
  have hmono :
      (MonoidWithZeroHom.valueMonoid (ValuativeExtension.mapValueGroupWithZero K[A] K[B]) :
        Set Γ[B]ˣ) ⊆ H := by
    intro u hu
    -- Read a unit of the value monoid as the image of a nonzero source value-group element.
    change ((u : Γ[B]) ∈ Set.range (ValuativeExtension.mapValueGroupWithZero K[A] K[B])) at hu
    rcases hu with ⟨a, ha⟩
    have ha0 : a ≠ 0 := by
      intro ha0
      have hu0 : (0 : Γ[B]) = u := by simpa [ha0] using ha
      exact u.ne_zero hu0.symm
    refine ⟨Units.mk0 a ha0, ?_⟩
    ext
    simpa [ha]
  -- `valueGroup` is the subgroup closure of the value monoid, so membership descends to `H`.
  have hH : γ ∈ H := (Subgroup.mem_closure.mp hγ) H hmono
  rcases hH with ⟨δ, rfl⟩
  exact ⟨δ, rfl⟩

/-- Helper for Lemma 15.112.2: valuation `1` in the target fraction field means the element comes
from a unit of the target discrete valuation ring. -/
lemma target_ring_unit_of_valuation_eq_one {z : K[B]}
    (hz : (ValuativeRel.valuation K[B]) z = 1) :
    ∃ w : Bˣ, algebraMap B K[B] (w : B) = z := by
  let v := ValuationRing.valuation B K[B]
  let e := ValuativeRel.ValueGroupWithZero.orderMonoidIso v
  have hzv : v z = 1 := by
    -- Translate the canonical valuative-rel valuation back to the valuation-ring valuation.
    have horder : e ((ValuativeRel.valuation K[B]) z) = e 1 := by simpa [hz]
    simpa [e, v, ValuativeRel.ValueGroupWithZero.orderMonoidIso_valuation_eq_restrict₀] using
      horder
  have hz0 : z ≠ 0 := by
    intro hz0
    have hzero : (0 : Γ[B]) = 1 := by simpa [hz0] using hz
    exact zero_ne_one hzero
  have hz_mem : z ∈ v.integer := by
    -- Valuation `1` is exactly the integrality bound `≤ 1`.
    rw [Valuation.mem_integer_iff]
    simpa [hzv]
  have hzinv_mem : z⁻¹ ∈ v.integer := by
    -- The inverse has the same valuation because `1⁻¹ = 1`.
    rw [Valuation.mem_integer_iff]
    exact le_of_eq <| by
      calc
        v z⁻¹ = (v z)⁻¹ := map_inv₀ v z
        _ = 1 := by simp [hzv]
  obtain ⟨b, hb⟩ := (ValuationRing.mem_integer_iff B K[B] z).1 hz_mem
  obtain ⟨c, hc⟩ := (ValuationRing.mem_integer_iff B K[B] z⁻¹).1 hzinv_mem
  have hbc : b * c = 1 := by
    -- Multiplying the two integral representatives recovers `1` in the fraction field.
    refine IsFractionRing.injective B K[B] ?_
    calc
      algebraMap B K[B] (b * c) = algebraMap B K[B] b * algebraMap B K[B] c := by simp
      _ = z * z⁻¹ := by rw [hb, hc]
      _ = algebraMap B K[B] 1 := by simp [hz0]
  have hcb : c * b = 1 := by simpa [mul_comm] using hbc
  have hbUnit : IsUnit b := IsUnit.of_mul_eq_one_right c hcb
  -- Package the integral representative as the required unit of `B`.
  refine ⟨hbUnit.unit, ?_⟩
  calc
    algebraMap B K[B] (hbUnit.unit : B) = algebraMap B K[B] b := by rw [hbUnit.unit_spec]
    _ = z := hb

/-- Helper for Lemma 15.112.2: a trivial value-group quotient class for a target-uniformizer
power yields a source fraction equal to that power up to a target-ring unit. -/
lemma exists_base_fraction_unit_mul_uniformizer_power_of_trivial_value_group_class
    (πB : B) (hπB : maximalIdeal B = Ideal.span ({πB} : Set B))
    {k : ℕ}
    (htriv :
      ((Quotient.mk''
        (Units.map (Valuation.toMonoidWithZeroHom (ValuativeRel.valuation K[B])).toMonoidHom
          (uniformizer_power_fraction_unit (B := B) πB hπB k))) : Q) =
      ((Quotient.mk'' (1 : Γ[B]ˣ)) : Q)) :
    ∃ x : K[A], ∃ w : Bˣ,
      algebraMap K[A] K[B] x =
        algebraMap B K[B] (w : B) * algebraMap B K[B] πB ^ k := by
  let c : K[B]ˣ := uniformizer_power_fraction_unit (B := B) πB hπB k
  have hmem :
      Units.map (Valuation.toMonoidWithZeroHom (ValuativeRel.valuation K[B])).toMonoidHom c ∈
        MonoidWithZeroHom.valueGroup (ValuativeExtension.mapValueGroupWithZero K[A] K[B]) := by
    -- Rewrite the trivial quotient-class statement in the direction that exposes `c` itself.
    have htriv' :
        ((Quotient.mk'' (1 : Γ[B]ˣ)) : Q) =
        ((Quotient.mk''
          (Units.map (Valuation.toMonoidWithZeroHom (ValuativeRel.valuation K[B])).toMonoidHom c)) :
          Q) := htriv.symm
    rw [QuotientGroup.eq] at htriv'
    simpa [c] using htriv'
  obtain ⟨δ, hδ⟩ := exists_source_value_group_unit_of_mem_valueGroup (A := A) (B := B) hmem
  let x : K[A] := Classical.choose (ValuativeRel.valuation_surjective (δ : Γ[A]))
  have hx : (ValuativeRel.valuation K[A]) x = δ := by
    exact Classical.choose_spec (ValuativeRel.valuation_surjective (δ : Γ[A]))
  have hx0 : x ≠ 0 := by
    intro hx0
    exact δ.ne_zero (by simpa [hx0] using hx.symm)
  let a : K[A]ˣ := Units.mk0 x hx0
  have hvala :
      Units.map (Valuation.toMonoidWithZeroHom (ValuativeRel.valuation K[A])).toMonoidHom a = δ := by
    -- Choose the unit representative whose valuation is exactly the source value-group unit.
    ext
    simp [a, x, hx]
  have hvaleq :
      Units.map (Valuation.toMonoidWithZeroHom (ValuativeRel.valuation K[B])).toMonoidHom
        (Units.map (algebraMap K[A] K[B]).toMonoidHom a) =
      Units.map (Valuation.toMonoidWithZeroHom (ValuativeRel.valuation K[B])).toMonoidHom c := by
    -- Compare the target valuation of the mapped source unit with the chosen target power.
    calc
      Units.map (Valuation.toMonoidWithZeroHom (ValuativeRel.valuation K[B])).toMonoidHom
          (Units.map (algebraMap K[A] K[B]).toMonoidHom a)
          =
        Units.map (ValuativeExtension.mapValueGroupWithZero K[A] K[B]).toMonoidHom
          (Units.map (Valuation.toMonoidWithZeroHom (ValuativeRel.valuation K[A])).toMonoidHom a) := by
            ext
            simp [ValuativeExtension.mapValueGroupWithZero]
      _ =
        Units.map (ValuativeExtension.mapValueGroupWithZero K[A] K[B]).toMonoidHom δ := by
          rw [hvala]
      _ =
        Units.map (Valuation.toMonoidWithZeroHom (ValuativeRel.valuation K[B])).toMonoidHom c := hδ
  have hratio_val :
      (ValuativeRel.valuation K[B])
        ((((Units.map (algebraMap K[A] K[B]).toMonoidHom a) * c⁻¹ : K[B]ˣ) : K[B])) = 1 := by
    -- Matching valuations means the quotient of the two fraction-field units has valuation `1`.
    have hratio_unit :
        Units.map (Valuation.toMonoidWithZeroHom (ValuativeRel.valuation K[B])).toMonoidHom
          ((Units.map (algebraMap K[A] K[B]).toMonoidHom a) * c⁻¹) = 1 := by
      rw [map_mul, map_inv, hvaleq]
      simp
    exact congrArg (fun u : Γ[B]ˣ ↦ (u : Γ[B])) hratio_unit
  obtain ⟨w, hw⟩ := target_ring_unit_of_valuation_eq_one (B := B) hratio_val
  have hk0 : algebraMap B K[B] πB ^ k ≠ 0 :=
    uniformizer_power_fraction_ne_zero (B := B) πB hπB k
  have hratio_eq :
      algebraMap B K[B] (w : B) =
        algebraMap K[A] K[B] x * (algebraMap B K[B] πB ^ k)⁻¹ := by
    -- Unfold the chosen source and target units back to the underlying fraction-field elements.
    simpa [a, c, uniformizer_power_fraction_unit, x, mul_assoc] using hw
  refine ⟨x, w, ?_⟩
  -- Multiply the unit-valued ratio by `πB ^ k` to recover the desired factorization.
  calc
    algebraMap K[A] K[B] x
        = algebraMap K[A] K[B] x * ((algebraMap B K[B] πB ^ k)⁻¹ *
            algebraMap B K[B] πB ^ k) := by simp [hk0]
    _ =
      (algebraMap K[A] K[B] x * (algebraMap B K[B] πB ^ k)⁻¹) *
        algebraMap B K[B] πB ^ k := by ac_rfl
    _ = algebraMap B K[B] (w : B) * algebraMap B K[B] πB ^ k := by rw [← hratio_eq]

/-- Helper for Lemma 15.112.2: if two target-uniformizer powers define the same class in the
value-group quotient, then the class of their exponent difference is trivial. -/
lemma uniformizer_power_difference_has_trivial_class_of_equal_classes
    (πB : B) (hπB : maximalIdeal B = Ideal.span ({πB} : Set B))
    {m n : ℕ} (hmn : m ≤ n)
    (hEq :
      ((Quotient.mk''
        (Units.map (Valuation.toMonoidWithZeroHom (ValuativeRel.valuation K[B])).toMonoidHom
          (uniformizer_power_fraction_unit (B := B) πB hπB m))) : Q) =
      ((Quotient.mk''
        (Units.map (Valuation.toMonoidWithZeroHom (ValuativeRel.valuation K[B])).toMonoidHom
          (uniformizer_power_fraction_unit (B := B) πB hπB n))) : Q)) :
    ((Quotient.mk''
      (Units.map (Valuation.toMonoidWithZeroHom (ValuativeRel.valuation K[B])).toMonoidHom
        (uniformizer_power_fraction_unit (B := B) πB hπB (n - m)))) : Q) =
    ((Quotient.mk'' (1 : Γ[B]ˣ)) : Q) := by
  let c : ℕ → K[B]ˣ := uniformizer_power_fraction_unit (B := B) πB hπB
  let v : K[B]ˣ →* Γ[B]ˣ :=
    Units.map (Valuation.toMonoidWithZeroHom (ValuativeRel.valuation K[B])).toMonoidHom
  have hdiff :
      (c m)⁻¹ * c n = c (n - m) := by
    have hπB0 : algebraMap B K[B] πB ≠ 0 := by
      -- The chosen uniformizer is nonzero, and the fraction-field map is injective.
      exact
        (map_ne_zero_iff (algebraMap B K[B]) (IsFractionRing.injective B K[B])).2
          ((IsDiscreteValuationRing.irreducible_iff_uniformizer πB).mpr hπB).ne_zero
    have hpowm0 : algebraMap B K[B] πB ^ m ≠ 0 := pow_ne_zero m hπB0
    -- Rewrite `n` as `m + (n - m)` and cancel the common factor.
    apply Units.ext
    change (algebraMap B K[B] πB ^ m)⁻¹ * algebraMap B K[B] πB ^ n =
        algebraMap B K[B] πB ^ (n - m)
    calc
      (algebraMap B K[B] πB ^ m)⁻¹ * algebraMap B K[B] πB ^ n
          =
        (algebraMap B K[B] πB ^ m)⁻¹ *
          (algebraMap B K[B] πB ^ m * algebraMap B K[B] πB ^ (n - m)) := by
            rw [← pow_add, Nat.add_sub_of_le hmn]
      _ =
        ((algebraMap B K[B] πB ^ m)⁻¹ * algebraMap B K[B] πB ^ m) *
          algebraMap B K[B] πB ^ (n - m) := by
            ac_rfl
      _ = algebraMap B K[B] πB ^ (n - m) := by simp [hpowm0]
  have hmem :
      (v (c m))⁻¹ * v (c n) ∈
        MonoidWithZeroHom.valueGroup (ValuativeExtension.mapValueGroupWithZero K[A] K[B]) := by
    -- Rewriting equality of quotient classes exposes the subgroup witness directly.
    rw [QuotientGroup.eq] at hEq
    simpa [v] using hEq
  have hmem_diff :
      v (c (n - m)) ∈
        MonoidWithZeroHom.valueGroup (ValuativeExtension.mapValueGroupWithZero K[A] K[B]) := by
    -- The subgroup witness is exactly the valuation of the difference power.
    have hvdiff : (v (c m))⁻¹ * v (c n) = v (c (n - m)) := by
      calc
        (v (c m))⁻¹ * v (c n) = v ((c m)⁻¹) * v (c n) := by rw [map_inv]
        _ = v ((c m)⁻¹ * c n) := by rw [← map_mul]
        _ = v (c (n - m)) := by rw [hdiff]
    exact hvdiff ▸ hmem
  have hOne :
      ((Quotient.mk'' (1 : Γ[B]ˣ)) : Q) =
      ((Quotient.mk'' (v (c (n - m)))) : Q) := by
    -- A subgroup element represents the trivial quotient class.
    rw [QuotientGroup.eq]
    simpa using hmem_diff
  simpa [c, v] using hOne.symm

/-- Helper for Lemma 15.112.2: allowing a target-ring unit factor does not affect the
ramification divisibility statement for a base-element equality. -/
lemma ramificationIndex_dvd_exponent_of_base_element_eq_target_unit_mul_uniformizer_power
    (πA : A) (πB : B)
    (hπA : maximalIdeal A = Ideal.span ({πA} : Set A))
    (hπB : maximalIdeal B = Ideal.span ({πB} : Set B))
    {a s : A} {m : ℕ} {w : Bˣ}
    (hs : s ≠ 0) (ha : a ≠ 0)
    (hEq : algebraMap A B a = algebraMap A B s * (w : B) * πB ^ m) :
    ramificationIndex A B ∣ m := by
  -- Compare the target-uniformizer exponents attached to the two source elements.
  obtain ⟨na, hna⟩ := algebraMap_associated_uniformizer_pow πA πB hπA hπB ha
  obtain ⟨ns, hns⟩ := algebraMap_associated_uniformizer_pow πA πB hπA hπB hs
  have hEqAssoc : Associated (algebraMap A B a) (algebraMap A B s * (w : B) * πB ^ m) :=
    associated_of_eq hEq
  have hs_unit :
      Associated (algebraMap A B s * (w : B)) (algebraMap A B s) := by
    -- The extra factor is a unit, so it does not change the associated class.
    refine Associated.trans (associated_of_eq (mul_comm _ _)) ?_
    exact associated_of_unit_mul_left w (algebraMap A B s)
  have hright :
      Associated (algebraMap A B s * (w : B) * πB ^ m)
        (πB ^ (ramificationIndex A B * ns + m)) := by
    -- After removing the unit, the remaining power-counting argument is unchanged.
    exact associated_mul_uniformizer_pow (Associated.trans hs_unit hns)
  have hpow :
      Associated (πB ^ (ramificationIndex A B * na))
        (πB ^ (ramificationIndex A B * ns + m)) := by
    exact Associated.trans (Associated.symm hna) (Associated.trans hEqAssoc hright)
  have hexp :
      ramificationIndex A B * na = ramificationIndex A B * ns + m :=
    uniformizer_power_associated_injective πB hπB hpow
  have hdivSum : ramificationIndex A B ∣ ramificationIndex A B * ns + m := by
    rw [← hexp]
    exact dvd_mul_of_dvd_left (dvd_refl (ramificationIndex A B)) na
  have hdivBase : ramificationIndex A B ∣ ramificationIndex A B * ns :=
    dvd_mul_of_dvd_left (dvd_refl (ramificationIndex A B)) ns
  -- Subtract the known multiple to isolate the remaining exponent.
  have hdivSub :
      ramificationIndex A B ∣
        (ramificationIndex A B * ns + m) - ramificationIndex A B * ns :=
    Nat.dvd_sub hdivSum hdivBase
  simpa using hdivSub

/-- Helper for Lemma 15.112.2: if a target-uniformizer power times a target-ring unit comes from
the base fraction field, then the exponent is divisible by the ramification index. -/
lemma ramificationIndex_dvd_exponent_of_base_fraction_eq_target_unit_mul_uniformizer_power
    (πA : A) (πB : B)
    (hπA : maximalIdeal A = Ideal.span ({πA} : Set A))
    (hπB : maximalIdeal B = Ideal.span ({πB} : Set B))
    {m : ℕ} {x : FractionRing A} {w : Bˣ}
    (hx : algebraMap (FractionRing A) (FractionRing B) x =
      algebraMap B (FractionRing B) (w : B) * algebraMap B (FractionRing B) πB ^ m) :
    ramificationIndex A B ∣ m := by
  -- Write the source fraction as `a / s` and clear denominators inside `B`.
  obtain ⟨⟨a, s⟩, hsx⟩ := IsLocalization.surj (nonZeroDivisors A) x
  have hs0 : (s : A) ≠ 0 := by
    exact (mem_nonZeroDivisors_iff_ne_zero).mp s.2
  have hs_map :
      algebraMap B (FractionRing B) (algebraMap A B (s : A)) =
        algebraMap (FractionRing A) (FractionRing B) (algebraMap A (FractionRing A) (s : A)) := by
    -- Compare the two scalar-tower routes for the denominator.
    calc
      algebraMap B (FractionRing B) (algebraMap A B (s : A)) =
          algebraMap A (FractionRing B) (s : A) := by
            simpa [RingHom.comp_apply] using
              (DFunLike.congr_fun (IsScalarTower.algebraMap_eq A B (FractionRing B)) (s : A)).symm
      _ =
          algebraMap (FractionRing A) (FractionRing B) (algebraMap A (FractionRing A) (s : A)) := by
            simpa [RingHom.comp_apply] using
              DFunLike.congr_fun
                (IsScalarTower.algebraMap_eq A (FractionRing A) (FractionRing B)) (s : A)
  have ha_map :
      algebraMap B (FractionRing B) (algebraMap A B a) =
        algebraMap (FractionRing A) (FractionRing B) (algebraMap A (FractionRing A) a) := by
    -- The numerator follows the same scalar-tower comparison.
    calc
      algebraMap B (FractionRing B) (algebraMap A B a) =
          algebraMap A (FractionRing B) a := by
            simpa [RingHom.comp_apply] using
              (DFunLike.congr_fun (IsScalarTower.algebraMap_eq A B (FractionRing B)) a).symm
      _ =
          algebraMap (FractionRing A) (FractionRing B) (algebraMap A (FractionRing A) a) := by
            simpa [RingHom.comp_apply] using
              DFunLike.congr_fun
                (IsScalarTower.algebraMap_eq A (FractionRing A) (FractionRing B)) a
  have hEqFrac :
      algebraMap B (FractionRing B) (algebraMap A B (s : A) * (w : B) * πB ^ m) =
        algebraMap B (FractionRing B) (algebraMap A B a) := by
    -- Clearing denominators produces an equality in `FractionRing B` with the same unit factor.
    calc
      algebraMap B (FractionRing B) (algebraMap A B (s : A) * (w : B) * πB ^ m) =
          algebraMap B (FractionRing B) (algebraMap A B (s : A)) *
            (algebraMap B (FractionRing B) (w : B) * algebraMap B (FractionRing B) πB ^ m) := by
              simp [mul_assoc]
      _ =
          algebraMap B (FractionRing B) (algebraMap A B (s : A)) *
            algebraMap (FractionRing A) (FractionRing B) x := by
              rw [hx]
      _ =
          algebraMap (FractionRing A) (FractionRing B)
            (algebraMap A (FractionRing A) (s : A)) *
            algebraMap (FractionRing A) (FractionRing B) x := by
              rw [hs_map]
      _ =
          algebraMap (FractionRing A) (FractionRing B)
            (algebraMap A (FractionRing A) (s : A) * x) := by
              simp
      _ =
          algebraMap (FractionRing A) (FractionRing B)
            (x * algebraMap A (FractionRing A) (s : A)) := by rw [mul_comm]
      _ =
          algebraMap (FractionRing A) (FractionRing B) (algebraMap A (FractionRing A) a) := by
            rw [hsx]
      _ = algebraMap B (FractionRing B) (algebraMap A B a) := by rw [ha_map]
  have hEqB :
      algebraMap A B (s : A) * (w : B) * πB ^ m = algebraMap A B a := by
    -- Injectivity of the fraction-field map brings the equality back down to `B`.
    exact IsFractionRing.injective B (FractionRing B) hEqFrac
  have hExt : IsExtensionOfDiscreteValuationRings A B := inferInstance
  have hsB0 : algebraMap A B s ≠ 0 := by
    exact (map_ne_zero_iff (algebraMap A B) hExt.algebraMap_injective).2 hs0
  have hpow0 : πB ^ m ≠ 0 := by
    exact pow_ne_zero m (by
      exact ((IsDiscreteValuationRing.irreducible_iff_uniformizer πB).mpr hπB).ne_zero)
  have ha0 : a ≠ 0 := by
    refine (map_ne_zero_iff (algebraMap A B) hExt.algebraMap_injective).1 ?_
    rw [← hEqB]
    exact mul_ne_zero (mul_ne_zero hsB0 w.ne_zero) hpow0
  exact ramificationIndex_dvd_exponent_of_base_element_eq_target_unit_mul_uniformizer_power
    πA πB hπA hπB hs0 ha0 hEqB.symm

/-- Helper for Lemma 15.112.2: the valuation-ring ramification index dominates the chapter-local
DVR ramification index. -/
lemma valuationRing_ramificationIndex_le :
    (ramificationIndex A B : ℕ∞) ≤ IsExtensionOfValuationRings.ramificationIndex A B := by
  -- Route correction: the abandoned `Module.Finite` route was stronger than the source statement.
  -- The remaining source-faithful task is to inject the `e` powers of a target uniformizer into
  -- the valuation-group quotient, so the quotient cardinal is at least `e`.
  classical
  obtain ⟨πA, _, hπA⟩ := exists_uniformizer_generator A
  obtain ⟨πB, _, hπB⟩ := exists_uniformizer_generator B
  let c : ℕ → K[B]ˣ := uniformizer_power_fraction_unit (B := B) πB hπB
  let q : Fin (ramificationIndex A B) → Q := fun i ↦
    ((Quotient.mk''
      (Units.map (Valuation.toMonoidWithZeroHom (ValuativeRel.valuation K[B])).toMonoidHom
        (c i))) : Q)
  have hq_inj : Function.Injective q := by
    intro i j hij
    rcases le_total i.1 j.1 with hij_le | hji_le
    · -- Equal quotient classes force the exponent difference `j - i` to have trivial class.
      have htriv :
          ((Quotient.mk''
            (Units.map (Valuation.toMonoidWithZeroHom (ValuativeRel.valuation K[B])).toMonoidHom
              (c (j.1 - i.1)))) : Q) =
          ((Quotient.mk'' (1 : Γ[B]ˣ)) : Q) := by
        simpa [c] using
          uniformizer_power_difference_has_trivial_class_of_equal_classes
            (A := A) (B := B) πB hπB hij_le hij
      obtain ⟨x, w, hx⟩ :=
        exists_base_fraction_unit_mul_uniformizer_power_of_trivial_value_group_class
          (A := A) (B := B) πB hπB htriv
      have hdiv : ramificationIndex A B ∣ j.1 - i.1 :=
        ramificationIndex_dvd_exponent_of_base_fraction_eq_target_unit_mul_uniformizer_power
          (A := A) (B := B) πA πB hπA hπB (w := w) hx
      have hlt : j.1 - i.1 < ramificationIndex A B := by
        exact lt_of_le_of_lt (Nat.sub_le _ _) j.2
      have hzero : j.1 - i.1 = 0 := Nat.eq_zero_of_dvd_of_lt hdiv hlt
      apply Fin.ext
      exact le_antisymm hij_le (Nat.sub_eq_zero_iff_le.mp hzero)
    · -- The symmetric case reduces to the same difference argument after swapping the indices.
      have htriv :
          ((Quotient.mk''
            (Units.map (Valuation.toMonoidWithZeroHom (ValuativeRel.valuation K[B])).toMonoidHom
              (c (i.1 - j.1)))) : Q) =
          ((Quotient.mk'' (1 : Γ[B]ˣ)) : Q) := by
        simpa [c] using
          uniformizer_power_difference_has_trivial_class_of_equal_classes
            (A := A) (B := B) πB hπB hji_le hij.symm
      obtain ⟨x, w, hx⟩ :=
        exists_base_fraction_unit_mul_uniformizer_power_of_trivial_value_group_class
          (A := A) (B := B) πB hπB htriv
      have hdiv : ramificationIndex A B ∣ i.1 - j.1 :=
        ramificationIndex_dvd_exponent_of_base_fraction_eq_target_unit_mul_uniformizer_power
          (A := A) (B := B) πA πB hπA hπB (w := w) hx
      have hlt : i.1 - j.1 < ramificationIndex A B := by
        exact lt_of_le_of_lt (Nat.sub_le _ _) i.2
      have hzero : i.1 - j.1 = 0 := Nat.eq_zero_of_dvd_of_lt hdiv hlt
      apply Fin.ext
      exact le_antisymm (Nat.sub_eq_zero_iff_le.mp hzero) hji_le
  have hcard :
      Cardinal.lift (Cardinal.mk (Fin (ramificationIndex A B))) ≤
        Cardinal.lift (Cardinal.mk Q) := by
    exact Cardinal.lift_mk_le'.2 ⟨⟨q, hq_inj⟩⟩
  have henat : ENat.card (Fin (ramificationIndex A B)) ≤ ENat.card Q := by
    -- Turn the injection into a cardinal inequality and then into an `ENat` inequality.
    have htoENat := OrderHomClass.monotone Cardinal.toENat hcard
    simpa [ENat.card, Cardinal.toENat_lift] using htoENat
  -- Identifying both sides with the relevant quotient cardinal finishes the comparison.
  calc
    (ramificationIndex A B : ℕ∞) = ENat.card (Fin (ramificationIndex A B)) := by
      simpa [ENat.card_eq_coe_fintype_card]
    _ ≤ ENat.card Q := henat
    _ = IsExtensionOfValuationRings.ramificationIndex A B := by rfl

/-- Lemma 15.112.2 (2): for an extension of discrete valuation rings `A ⊂ B`, if the induced
fraction-field extension `FractionRing B / FractionRing A` is finite, then the ramification index
times the residue degree is bounded by `[FractionRing B : FractionRing A]`. This is the
source-facing DVR restatement of the canonical valuation-ring inequality from `Lemma_15_124_2`. -/
theorem ramificationIndex_mul_residueDegree_le_finrank_of_finiteDimensional_fractionField_extension
    [FiniteDimensional (FractionRing A) (FractionRing B)] :
    ramificationIndex A B * residueDegree A B ≤
      Module.finrank (FractionRing A) (FractionRing B) := by
  let _ : IsExtensionOfValuationRings A B := inferInstance
  have hcore :
      IsExtensionOfValuationRings.ramificationIndex A B *
          IsExtensionOfValuationRings.residueDegree A B ≤
        Module.finrank (FractionRing A) (FractionRing B) :=
    _root_.ramificationIndex_mul_residueDegree_le_finrank_of_finiteDimensional_fractionField_extension
      (A := A) (B := B)
  have hram :
      ((ramificationIndex A B : ℕ∞) * residueDegree A B : ℕ∞) ≤
        Module.finrank (FractionRing A) (FractionRing B) := by
    -- First compare the two ramification-index owners, then feed the result into the imported
    -- valuation-ring inequality.
    calc
      (ramificationIndex A B : ℕ∞) * residueDegree A B
          ≤ IsExtensionOfValuationRings.ramificationIndex A B * residueDegree A B := by
            gcongr
            exact valuationRing_ramificationIndex_le (A := A) (B := B)
      _ = IsExtensionOfValuationRings.ramificationIndex A B *
            IsExtensionOfValuationRings.residueDegree A B := by
            rfl
      _ ≤ Module.finrank (FractionRing A) (FractionRing B) := hcore
  -- Convert the `ℕ∞` inequality back to the chapter's natural-number statement.
  simpa using ENat.toNat_le_of_le_coe hram

end IsExtensionOfDiscreteValuationRings

end
