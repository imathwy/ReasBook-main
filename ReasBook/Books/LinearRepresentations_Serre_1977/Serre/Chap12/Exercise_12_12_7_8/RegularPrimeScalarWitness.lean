import LinearRepresentations_Serre_1977.Chap12.Exercise_12_12_7_8.RegularPrimeResidueEvaluation
import LinearRepresentations_Serre_1977.Chap12.Exercise_12_12_7_8.RegularPrimeFiberSeparators

open scoped Representation

noncomputable section

universe v w

namespace Representation

section

variable {G : Type w} [Group G] [Finite G]
variable {A : Type v} [CommRing A]
variable {L : Type w} [Field L] [NumberField L]
variable [IsCyclotomicExtension {Monoid.exponent G} ℚ L]

variable (K : IntermediateField ℚ L)
variable [Algebra A K]

local notation "ΓK" => (Representation.exerciseGammaSubgroup (G := G) (L := L) K)

variable [IsDomain A] [Ring.HasFiniteQuotients A] [IsFractionRing A K]
variable [IsIntegralClosure A ℤ K]

section RegularPrime

variable {p : Nat.Primes}

/-- Helper for Exercise 12-12.7-8: once Serre's fixed-fiber evaluator is known to have trivial
kernel, the separator-based surjectivity theorem upgrades it to the expected algebra equivalence
with the function ring on `p`-regular `Γ_K`-classes. -/
noncomputable def
    fixed_maximal_fiber_algEquiv_pregular_galoisPowerClass_functions_of_injective
    (M : NonzeroResidualCharacteristicMaximalIdeal A p)
    (hinj :
      Function.Injective (regular_fiber_eval_family_algHom (A := A) (K := K) (G := G) M)) :
    (M.1.asIdeal.Fiber
      (characterRingOverFieldAlgebraScalarExtensionSubalgebra A K G)) ≃ₐ[M.1.asIdeal.ResidueField]
        (PRegularGaloisPowerClass ΓK p → M.1.asIdeal.ResidueField) :=
  -- Once the kernel is known to be zero, Serre's separator characters already supply the
  -- surjective half of the fixed-fiber identification.
  AlgEquiv.ofBijective
    (regular_fiber_eval_family_algHom (A := A) (K := K) (G := G) M)
    ⟨hinj, regular_fiber_eval_family_surjective_from_separators (A := A) (K := K) (G := G) M⟩

end RegularPrime

end

end Representation
