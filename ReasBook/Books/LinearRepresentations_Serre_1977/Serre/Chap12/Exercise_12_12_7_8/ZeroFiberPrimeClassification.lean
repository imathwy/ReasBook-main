import LinearRepresentations_Serre_1977.Chap12.Exercise_12_12_7_8.ZeroFiberClassification

open scoped Representation

noncomputable section

universe u v w

namespace Representation

section

variable {G : Type u} [Group G] [Finite G]
variable {A : Type v} [CommRing A]
variable {L : Type w} [Field L] [NumberField L]
variable [IsCyclotomicExtension {Monoid.exponent G} ℚ L]

variable (K : IntermediateField ℚ L)
variable [Algebra A K]

/-- Helper for Exercise 12-12.7-8: a private `Fintype` witness for the finite group `G`. -/
private def instFintypeExercise121278ZeroFiberPrimeClassificationGroup : Fintype G :=
  Fintype.ofFinite G
attribute [local instance] instFintypeExercise121278ZeroFiberPrimeClassificationGroup

local notation "ΓK" => (Representation.exerciseGammaSubgroup (G := G) (L := L) K)
local notation "SpecAKG" =>
  PrimeSpectrum (characterRingOverFieldAlgebraScalarExtensionSubalgebra A K G)

variable [IsDomain A] [Ring.HasFiniteQuotients A] [IsFractionRing A K]

/-- Helper for Exercise 12-12.7-8: once primes of the bottom fiber are classified by
`Γ_K`-classes, the zero-contraction branch follows by transporting that fiberwise classification
back to `Spec (A ⊗ R_K(G))`. -/
theorem exists_eq_galoisPowerClassScalarExtensionZeroPrimeIdeal_of_comap_eq_bot_of_zeroFiberClassification
    (hclass :
      ∀ q :
        PrimeSpectrum
          (((⊥ : Ideal A).Fiber
            (characterRingOverFieldAlgebraScalarExtensionSubalgebra A K G))),
        ∃ c : GaloisPowerClass ΓK,
          zero_fiber_prime_to_specAKG (A := A) (K := K) (G := G) q =
            galoisPowerClassScalarExtensionZeroPrimeIdeal K c)
    {𝔭 : SpecAKG}
    (h𝔭 :
      Ideal.comap (algebraMap A (characterRingOverFieldAlgebraScalarExtensionSubalgebra A K G))
        𝔭.asIdeal = ⊥) :
    ∃ c : GaloisPowerClass ΓK, galoisPowerClassScalarExtensionZeroPrimeIdeal K c = 𝔭 := by
  let q := prime_over_bot_to_fiber (A := A) (K := K) (G := G) 𝔭 h𝔭
  -- Apply the fiberwise classification to the packaged point of the bottom fiber.
  obtain ⟨c, hc⟩ := hclass q
  refine ⟨c, ?_⟩
  calc
    galoisPowerClassScalarExtensionZeroPrimeIdeal K c
      = zero_fiber_prime_to_specAKG (A := A) (K := K) (G := G) q := by
          simpa using hc.symm
    _ = 𝔭 := by
          simpa [q] using
            zero_fiber_prime_to_specAKG_prime_over_bot_to_fiber
              (A := A) (K := K) (G := G) 𝔭 h𝔭

/-- Helper for Exercise 12-12.7-8: the genuine missing zero-branch input is a classification of
bottom-fiber primes by `Γ_K`-classes after transporting the bottom fiber to the corresponding
function ring. -/
private theorem zero_fiber_prime_classification
    (q :
      PrimeSpectrum
        (((⊥ : Ideal A).Fiber
          (characterRingOverFieldAlgebraScalarExtensionSubalgebra A K G)))) :
    ∃ c : GaloisPowerClass ΓK,
      zero_fiber_prime_to_specAKG (A := A) (K := K) (G := G) q =
        galoisPowerClassScalarExtensionZeroPrimeIdeal K c := by
  let e :=
    zero_fiber_algEquiv_galoisPowerClass_functions
      (A := A) (K := K) (G := G)
  have htransport :
      ∀ c : GaloisPowerClass ΓK,
        zero_fiber_prime_to_specAKG (A := A) (K := K) (G := G)
            (zero_fiber_lift (A := A) (K := K) (G := G) e c) =
          galoisPowerClassScalarExtensionZeroPrimeIdeal K c := by
    intro c
    -- Once the transported evaluation map is identified with Serre's owner map, the zero-prime
    -- equality is exactly the packaged kernel comparison.
    exact
      transported_zero_fiber_eval_prime_eq_zero_prime_of_evalAlgHom_eq
        (A := A) (K := K) (G := G) e c
        (transported_zero_fiber_evalAlgHom_eq_zeroPrimeIdealEval
          (A := A) (K := K) (G := G) c)
  -- The remaining zero branch is the abstract bottom-fiber transport theorem.
  exact
    zero_fiber_prime_classification_of_algEquiv
      (A := A) (K := K) (G := G) e htransport q

/-- Helper for Exercise 12-12.7-8: a prime of `A ⊗ R_K(G)` whose contraction to `A` is zero must
be one of Serre's zero-residual primes `P₀,c`. -/
theorem exists_eq_galoisPowerClassScalarExtensionZeroPrimeIdeal_of_comap_eq_bot
    {𝔭 : SpecAKG}
    (h𝔭 :
      Ideal.comap (algebraMap A (characterRingOverFieldAlgebraScalarExtensionSubalgebra A K G))
        𝔭.asIdeal = ⊥) :
    ∃ c : GaloisPowerClass ΓK, galoisPowerClassScalarExtensionZeroPrimeIdeal K c = 𝔭 := by
  -- The zero branch is delegated entirely to the bottom-fiber classification helper above.
  exact
    exists_eq_galoisPowerClassScalarExtensionZeroPrimeIdeal_of_comap_eq_bot_of_zeroFiberClassification
      (A := A) (K := K) (G := G)
      (hclass := zero_fiber_prime_classification (A := A) (K := K) (G := G))
      h𝔭

end

end Representation
