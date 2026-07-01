import Mathlib
import stacks_project.Chap10.Lemma_10_32_4
import stacks_project.Chap10.Lemma_10_108_2

-- Declarations for this item will be appended below by the statement pipeline.

universe u

section

open Ideal.Quotient

variable {R : Type u} [CommRing R]

private theorem exists_pow_eq_iff_exists_pow_eq_unit {A : Type u} [CommRing A]
    {n : ℕ} (hn : 1 ≤ n) {a : A} (ha : IsUnit a) :
    (∃ b : A, b ^ n = a) ↔ ∃ u : Aˣ, u ^ n = ha.unit := by
  constructor
  · rintro ⟨b, hb⟩
    have hb_pow_unit : IsUnit (b ^ n) := by
      simpa [hb] using ha
    have hb_unit : IsUnit b :=
      (isUnit_pow_iff (Nat.one_le_iff_ne_zero.mp hn)).mp hb_pow_unit
    refine ⟨hb_unit.unit, ?_⟩
    apply Units.ext
    change ((hb_unit.unit : A) ^ n) = a
    simp [hb]
  · rintro ⟨u, hu⟩
    refine ⟨(u : A), ?_⟩
    simpa [ha.unit_spec] using congrArg (fun v : Aˣ ↦ (v : A)) hu

private theorem one_add_pow_sub_one_mem (I : Ideal R) (n : ℕ) (x : I) :
    (1 + (x : R)) ^ n - 1 ∈ I := by
  rw [← eq_zero_iff_mem]
  have hx0 : mk I (x : R) = 0 := eq_zero_iff_mem.mpr x.property
  simp [hx0]

-- Proof sketch: construct the inverse by the truncated binomial series for `(1 + x)^(1 / n)`;
-- local nilpotence makes the series finite, and `n` is invertible in `R` because it is
-- invertible in `R ⧸ I` and units lift across locally nilpotent ideals by Lemma 10.32.4.
/-- Lemma 10.32.8 (1), canonical form: if `I` is locally nilpotent and `n ≥ 1` is invertible in
`R ⧸ I`, then the `n`th-power map on the canonical owner object `1 + I` is bijective. -/
theorem bijective_pow_one_add_of_isLocallyNilpotent (I : Ideal R)
    (hI : I.IsLocallyNilpotent) {n : ℕ} (hn : 1 ≤ n)
    (hn_unit : IsUnit (n : R ⧸ I)) :
    Function.Bijective (fun x : Ideal.oneAdd I ↦ x ^ n) := sorry

/-- Ideal-subtype bridge: under the coordinate identification `x ↦ 1 + x` between `I` and `1 + I`,
the canonical power map on `1 + I` is the textbook map `x ↦ (1 + x)^n - 1` on `I`. -/
theorem bijective_one_add_pow_sub_one_of_isLocallyNilpotent (I : Ideal R)
    (hI : I.IsLocallyNilpotent) {n : ℕ} (hn : 1 ≤ n)
    (hn_unit : IsUnit (n : R ⧸ I)) :
    Function.Bijective fun x : I ↦
      show I from ⟨(1 + (x : R)) ^ n - 1, one_add_pow_sub_one_mem I n x⟩ := sorry

-- Proof sketch: pass between roots in `R` and roots in `R ⧸ I` through the unit groups, then use
-- the owner-level bijectivity statement on `1 + I` from part (1).
/-- Lemma 10.32.8 (2), canonical form: for a locally nilpotent ideal `I`, an `n`th root of a
unit of `R` exists if and only if an `n`th root exists after mapping that unit to `(R ⧸ I)ˣ`. -/
theorem units_exists_pow_eq_iff_exists_pow_eq_quotient_of_isLocallyNilpotent
    (I : Ideal R) (hI : I.IsLocallyNilpotent) {n : ℕ} (hn : 1 ≤ n)
    (hn_unit : IsUnit (n : R ⧸ I))
    (a : Rˣ) :
    (∃ b : Rˣ, b ^ n = a) ↔
      ∃ bbar : (R ⧸ I)ˣ, bbar ^ n = Units.map (mk I).toMonoidHom a := sorry

-- Proof sketch: if `a = b^n`, then its image in `R ⧸ I` is the `n`th power of the image of `b`.
-- Conversely, if the image of `a` is `b̄^n`, lift `b̄` to `b : R`, use Lemma 10.32.4 to see that
-- `b` is a unit, and then apply part (1) to the element `a * b⁻n` lying in `1 + I`.
/-- Unit-valued bridge: a unit of `R` is an `n`th power if and only if its image in `R ⧸ I` is an
`n`th power. -/
theorem isUnit_exists_pow_eq_iff_exists_pow_eq_quotient_of_isLocallyNilpotent
    (I : Ideal R) (hI : I.IsLocallyNilpotent) {n : ℕ} (hn : 1 ≤ n)
    (hn_unit : IsUnit (n : R ⧸ I))
    {a : R} (ha : IsUnit a) :
    (∃ b : R, b ^ n = a) ↔ ∃ bbar : R ⧸ I, bbar ^ n = mk I a := by
  have hqa : IsUnit (mk I a) := ha.map (mk I)
  have hmap : hqa.unit = Units.map (mk I).toMonoidHom ha.unit := by
    apply Units.ext
    simp
  rw [exists_pow_eq_iff_exists_pow_eq_unit hn ha,
    exists_pow_eq_iff_exists_pow_eq_unit hn hqa]
  simpa [hmap] using
    units_exists_pow_eq_iff_exists_pow_eq_quotient_of_isLocallyNilpotent I hI hn hn_unit ha.unit

end
