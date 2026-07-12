import LinearRepresentations_Serre_1977.Chap12.Exercise_12_12_7_8

open scoped Representation

noncomputable section

universe u v w

namespace Representation

section

variable {G : Type u} [Group G] [Finite G]
variable {A : Type v} [CommRing A] [IsDomain A] [Ring.HasFiniteQuotients A]
variable {L : Type w} [Field L] [NumberField L]
variable [IsCyclotomicExtension {Monoid.exponent G} ℚ L]
variable (K : IntermediateField ℚ L)
variable [Algebra A K] [IsFractionRing A K]

local notation "ΓK" => Γ[K](G)
local notation "SpecAKG" =>
  PrimeSpectrum (characterRingOverFieldAlgebraScalarExtensionSubalgebra A K G)

-- Route correction (faithfulness): the former
-- `fixedMaximalFiberAlgEquivPRegularGaloisPowerClassFunctions_nonempty` asserted a FALSE statement —
-- that the fixed fiber over `M` is *algebra*-isomorphic to the residue-field function ring on
-- `p`-regular `Γ_K`-classes.  That is false once `p ∣ |G|`: the fiber is a finite NON-reduced
-- `κ(M)`-algebra of rank equal to the number of *all* `Γ_K`-power classes, strictly larger than the
-- number of `p`-regular ones.  The correct (true) statement is the SPECTRUM-level equivalence
-- `Representation.fixed_maximal_fiber_primeSpectrum_equiv_pRegularGaloisPowerClass` in
-- `Serre.Chap12.Exercise_12_12_7_8`; the false algebra-isomorphism has been removed.

-- Route correction: the owner theorem
-- `Representation.transportedRegularFiberEvalPrime_is_regularPrime` is already provided by the
-- imported Chapter 12 regular-fiber API, so this infrastructure file no longer redeclares it.

/-- Infrastructure for Exercise 12-12.7-8: every prime over a fixed nonzero maximal ideal is one
of the transported evaluation primes on `p`-regular `Γ_K`-classes.

Proof route from Serre, Ch. 12, Sec. 7:
1. Package `P` as a point of the fiber over `M` using
   `PrimeSpectrum.primesOverOrderIsoFiber` and the comap equality `hP`.
2. Choose the fixed-fiber equivalence from
   `fixedMaximalFiberAlgEquivPRegularGaloisPowerClassFunctions_nonempty` and push the fiber prime
   forward to a prime of the finite product ring
   `PRegularGaloisPowerClass ΓK p → M.ResidueField`.
3. A finite product of fields has primes exactly the coordinate kernels.  Use
   `PrimeSpectrum.exists_comap_evalRingHom_eq` and the fact that a field has only the zero prime to
   get some coordinate `c`.
4. Pull the coordinate prime back through the same two equivalences.  The resulting prime is `P`
   by inverse-map cancellation in `PrimeSpectrum.primesOverOrderIsoFiber`.
5. Apply `transportedRegularFiberEvalPrime_is_regularPrime` to translate the transported
   coordinate-kernel statement into Serre's predicate
   `IsGaloisPowerClassScalarExtensionRegularPrime K M c P`. -/
theorem exists_regularPrime_of_comap_eq_fixed_maximal
    {p : Nat.Primes} (M : NonzeroResidualCharacteristicMaximalIdeal A p)
    {P : SpecAKG}
    (hP :
      Ideal.comap
          (algebraMap A (characterRingOverFieldAlgebraScalarExtensionSubalgebra A K G))
          P.asIdeal = M.1.asIdeal) :
    ∃ c : PRegularGaloisPowerClass ΓK p,
      IsGaloisPowerClassScalarExtensionRegularPrime K M c P := by
  -- Route correction: reuse the compiled owner classification over the fixed fiber, then turn the
  -- resulting equality with the indexed owner prime back into Serre's intrinsic predicate.
  obtain ⟨c, hc⟩ := exists_eq_galoisPowerClassScalarExtensionRegularPrime_of_comap_eq_fixed_maximal K M hP
  refine ⟨c, ?_⟩
  simpa [hc] using galoisPowerClassScalarExtensionRegularPrime_spec K M c

end

end Representation
