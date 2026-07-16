import Mathlib
import StacksProject_2024.stacks_project.Chap10.Lemma_10_25_1

-- Declarations for this item will be appended below by the statement pipeline.

universe u

section

variable {R : Type u} [CommRing R] [IsReduced R]

local instance (p : minimalPrimes R) : p.1.IsPrime :=
  Ideal.minimalPrimes_isPrime p.2

private theorem radical_bot_eq_bot : (⊥ : Ideal R).radical = ⊥ := by
  simpa [nilradical, Ideal.zero_eq_bot] using nilradical_eq_zero R

-- Proof sketch: the `p`-component of the canonical `algebraMap` into the product is the
-- localization map
-- `R → Localization.AtPrime p`, whose kernel is `p` by
-- `Localization.AtPrime.comap_maximalIdeal`. Intersecting these kernels over all minimal primes
-- gives `⊥`, since `R` is reduced and the intersection of the minimal primes is zero.
/-- The canonical map from `R` to the product of the localizations `R_𝔭` over all minimal
primes `𝔭` is injective. -/
private theorem algebraMap_minimalPrimeLocalizations_injective :
    Function.Injective (algebraMap R (∀ p : minimalPrimes R, Localization.AtPrime p.1)) := by
  intro x y hxy
  have hxy' : x - y ∈ sInf (minimalPrimes R) := by
    rw [Ideal.mem_sInf]
    intro p hp
    haveI : p.IsPrime := Ideal.minimalPrimes_isPrime hp
    have hcomp : algebraMap R (Localization.AtPrime p) (x - y) = 0 := by
      have hcomp' := congrArg (fun f ↦ f ⟨p, hp⟩) hxy
      simpa [map_sub] using sub_eq_zero.mpr hcomp'
    obtain ⟨s, hs⟩ :=
      (IsLocalization.map_eq_zero_iff p.primeCompl (Localization.AtPrime p) (x - y)).mp hcomp
    have hmul : (s : R) * (x - y) ∈ p := by
      rw [hs]
      exact p.zero_mem
    exact (Ideal.IsPrime.mem_or_mem inferInstance hmul).resolve_left s.property
  rw [show minimalPrimes R = (⊥ : Ideal R).minimalPrimes by rfl,
    Ideal.sInf_minimalPrimes, radical_bot_eq_bot, Ideal.mem_bot] at hxy'
  exact sub_eq_zero.mp hxy'

/-- Lemma 10.25.2 (2): the canonical map to the product of the localizations at minimal primes
embeds `R` into a product of fields. -/
theorem algebraMap_embedding_into_product_of_fields :
    Function.Injective (algebraMap R (∀ p : minimalPrimes R, Localization.AtPrime p.1)) ∧
      ∀ p : minimalPrimes R, IsField (Localization.AtPrime p.1) := by
  refine ⟨algebraMap_minimalPrimeLocalizations_injective, ?_⟩
  exact isField_localizationAtPrime_of_minimalPrime

/-- Lemma 10.25.2 (1): a reduced ring admits an injective ring hom into a product of fields. -/
theorem exists_injective_ringHom_into_product_of_fields :
    ∃ f : R →+* ∀ p : minimalPrimes R, Localization.AtPrime p.1,
      Function.Injective f ∧
        ∀ p : minimalPrimes R, IsField (Localization.AtPrime p.1) := by
  exact ⟨algebraMap R (∀ p : minimalPrimes R, Localization.AtPrime p.1),
    algebraMap_embedding_into_product_of_fields⟩

-- Proof sketch: specialize `Ideal.iUnion_minimalPrimes` to `I = ⊥`; because `R` is reduced, the
-- radical of `⊥` is `⊥`, so the right-hand side simplifies to the complement of
-- `nonZeroDivisors R`.
/-- Lemma 10.25.2 (3), canonical form: the union of the minimal prime ideals of a reduced ring is
exactly the complement of `nonZeroDivisors R`. -/
theorem iUnion_minimalPrimes_eq_setOf_notMem_nonZeroDivisors :
    (⋃ p ∈ minimalPrimes R, (p : Set R)) = { x | x ∉ nonZeroDivisors R } := by
  rw [show minimalPrimes R = (⊥ : Ideal R).minimalPrimes by rfl]
  rw [Ideal.iUnion_minimalPrimes]
  ext x
  have hx : x ∉ nonZeroDivisors R ↔ { y | x * y = 0 ∧ y ≠ 0 }.Nonempty :=
    notMem_nonZeroDivisors_iff_left
  simpa [radical_bot_eq_bot, Set.nonempty_def, and_comm] using hx.symm

-- Proof sketch: rewrite the canonical zerodivisor statement using
-- `notMem_nonZeroDivisors_iff_left`.
/-- Lemma 10.25.2 (3), specification form: the union of the minimal prime ideals of a reduced ring
is exactly the set of zerodivisors. -/
theorem iUnion_minimalPrimes_eq_setOf_exists_mul_eq_zero :
    (⋃ p ∈ minimalPrimes R, (p : Set R)) = { x | ∃ y, y ≠ 0 ∧ x * y = 0 } := by
  ext x
  rw [iUnion_minimalPrimes_eq_setOf_notMem_nonZeroDivisors]
  have hx : x ∉ nonZeroDivisors R ↔ { y | x * y = 0 ∧ y ≠ 0 }.Nonempty :=
    notMem_nonZeroDivisors_iff_left
  simpa [Set.nonempty_def, and_comm] using hx

end
