import StacksProject_2024.Chap10.Example_10_119_5.CoefficientDVRCompletion

noncomputable section

universe u

open PowerSeries IsLocalRing
open AdicCompletion
open scoped Pointwise

variable (k : Type u) [Field k] (p : ℕ) [Fact p.Prime] [ExpChar k p]

open scoped PthPowerSubfield

local notation "A" => finitePthPowerCoefficientSubring k p

/-- Helper for Chap10 Example 10 119 5: the fraction-field extension
`Frac(A) ⊆ Frac(k[[X]])` is purely inseparable. -/
theorem finitePthPowerCoefficientSubring_fractionRing_isPurelyInseparable :
    IsPurelyInseparable (FractionRing ↥A) (FractionRing (PowerSeries k)) := by
  -- Install characteristic-`p` instances on the coefficient ring and its fraction field.
  haveI : CharP k p := by
    cases (inferInstance : ExpChar k p) with
    | zero =>
        exact False.elim (Nat.not_prime_one (Fact.out : Nat.Prime 1))
    | prime _ =>
        infer_instance
  haveI : CharP (PowerSeries k) p :=
    charP_of_injective_ringHom (PowerSeries.C_injective (R := k)) p
  have hAInjective : Function.Injective (algebraMap ↥A (PowerSeries k)) := by
    intro x y h
    exact Subtype.ext h
  haveI : CharP ↥A p :=
    RingHom.charP (algebraMap ↥A (PowerSeries k)) hAInjective p
  haveI : CharP (FractionRing ↥A) p :=
    IsFractionRing.charP_of_isFractionRing ↥A p
  haveI : ExpChar (FractionRing ↥A) p := ExpChar.prime (Fact.out : p.Prime)
  -- In characteristic `p`, it suffices to show every element has a `p`th power in the base field.
  rw [isPurelyInseparable_iff_pow_mem (FractionRing ↥A) p]
  intro x
  obtain ⟨a, b, _hb, rfl⟩ := IsFractionRing.div_surjective (PowerSeries k) x
  refine ⟨1, ?_⟩
  simp only [pow_one]
  -- Numerator and denominator have `p`th powers in `A`, so their quotient is a base element.
  let ap : ↥A :=
    ⟨(a : PowerSeries k) ^ p,
      pow_mem_finitePthPowerCoefficientSubring k p (a : PowerSeries k)⟩
  let bp : ↥A :=
    ⟨(b : PowerSeries k) ^ p,
      pow_mem_finitePthPowerCoefficientSubring k p (b : PowerSeries k)⟩
  let y : FractionRing ↥A :=
    algebraMap ↥A (FractionRing ↥A) ap / algebraMap ↥A (FractionRing ↥A) bp
  have hap : algebraMap ↥A (PowerSeries k) ap = a ^ p := by
    ext
    rfl
  have hbp : algebraMap ↥A (PowerSeries k) bp = b ^ p := by
    ext
    rfl
  have hy_map :
      algebraMap (FractionRing ↥A) (FractionRing (PowerSeries k)) y =
        algebraMap (PowerSeries k) (FractionRing (PowerSeries k)) (a ^ p) /
          algebraMap (PowerSeries k) (FractionRing (PowerSeries k)) (b ^ p) := by
    have hnonzero :
        nonZeroDivisors ↥A ≤
          (nonZeroDivisors (PowerSeries k)).comap
            (algebraMap ↥A (PowerSeries k)) :=
      nonZeroDivisors_le_comap_nonZeroDivisors_of_injective
        (algebraMap ↥A (PowerSeries k)) hAInjective
    have hmap_ap :
        algebraMap (FractionRing ↥A) (FractionRing (PowerSeries k))
            (algebraMap ↥A (FractionRing ↥A) ap) =
          algebraMap (PowerSeries k) (FractionRing (PowerSeries k))
            (algebraMap ↥A (PowerSeries k) ap) := by
      simpa [finitePthPowerCoefficientSubring_fractionRingAlgebra, IsFractionRing.map] using
        (IsLocalization.map_eq
          (Q := FractionRing (PowerSeries k))
          (g := algebraMap ↥A (PowerSeries k))
          (T := nonZeroDivisors (PowerSeries k)) hnonzero ap)
    have hmap_bp :
        algebraMap (FractionRing ↥A) (FractionRing (PowerSeries k))
            (algebraMap ↥A (FractionRing ↥A) bp) =
          algebraMap (PowerSeries k) (FractionRing (PowerSeries k))
            (algebraMap ↥A (PowerSeries k) bp) := by
      simpa [finitePthPowerCoefficientSubring_fractionRingAlgebra, IsFractionRing.map] using
        (IsLocalization.map_eq
          (Q := FractionRing (PowerSeries k))
          (g := algebraMap ↥A (PowerSeries k))
          (T := nonZeroDivisors (PowerSeries k)) hnonzero bp)
    simp [y, hmap_ap, hmap_bp, hap, hbp]
  refine ⟨y, ?_⟩
  -- The fraction-field map respects quotients, and powers distribute over division.
  calc
    algebraMap (FractionRing ↥A) (FractionRing (PowerSeries k)) y =
        algebraMap (PowerSeries k) (FractionRing (PowerSeries k)) (a ^ p) /
          algebraMap (PowerSeries k) (FractionRing (PowerSeries k)) (b ^ p) := hy_map
    _ = (algebraMap (PowerSeries k) (FractionRing (PowerSeries k)) a /
          algebraMap (PowerSeries k) (FractionRing (PowerSeries k)) b) ^ p := by
        rw [map_pow, map_pow, div_pow]
