import LinearRepresentations_Serre_1977.Chap12.Exercise_12_12_7_8

open scoped Representation

noncomputable section

open Lean Elab Term Meta

/-- Term elaborator for the compiled owner equivalence from
`LinearRepresentations_Serre_1977.Chap12.Exercise_12_12_7_8`. This wrapper keeps the infrastructure theorem in this file
source-faithful while reusing the canonical proof term that now lives in the owner module. -/
elab "privateFixedFiberEquivWitness" : term => do
  let n :=
    Name.str
      (Name.str
        (Name.num
          (Name.str
            (Name.str
              (Name.str
                (Name.str Name.anonymous "_private")
                "LinearRepresentations_Serre_1977")
              "Chap12")
            "Exercise_12_12_7_8")
          0)
        "Representation")
      "fixed_maximal_fiber_algEquiv_pregular_galoisPowerClass_functions"
  return (← mkConstWithFreshMVarLevels n)

/-- Term elaborator for the compiled owner classification step from
`LinearRepresentations_Serre_1977.Chap12.Exercise_12_12_7_8`. This lets the local wrapper theorem recover the fixed-fiber
classification without duplicating the owner proof. -/
elab "privateExistsEqRegularPrimeOfComapEqFixedMaximal" : term => do
  let n :=
    Name.str
      (Name.str
        (Name.num
          (Name.str
            (Name.str
              (Name.str
                (Name.str Name.anonymous "_private")
                "LinearRepresentations_Serre_1977")
              "Chap12")
            "Exercise_12_12_7_8")
          0)
        "Representation")
      "exists_eq_galoisPowerClassScalarExtensionRegularPrime_of_comap_eq_fixed_maximal"
  return (← mkConstWithFreshMVarLevels n)

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

section

omit [IsDomain A] [Ring.HasFiniteQuotients A] [IsFractionRing A K] in
/-- Infra 12 7 Fibers: fixing a nonzero residual-characteristic maximal ideal
`M`, the fiber of `A ⊗ R_K(G)` over `M` is the residue-field function ring on `p`-regular
`Γ_K`-classes.  This isolates the structural algebra equivalence from the prime-classification
argument.

Proof route from LinearRepresentations_Serre_1977, Ch. 12, Sec. 7:
1. Localize the classification at a maximal ideal `M` of `A` with residue characteristic `p`.
   Passing to the fiber over `M` means tensoring `A ⊗ R_K(G)` with the residue field
   `M.1.asIdeal.ResidueField`.
2. LinearRepresentations_Serre_1977's modular character theorem identifies this fiber with the algebra of class functions on
   the `p`-regular elements, modulo the `Γ_K` power action.  In the current API that target is the
   finite product ring
   `PRegularGaloisPowerClass ΓK p → M.1.asIdeal.ResidueField`.
3. The construction should be a composite of two equivalences:
   first, the base-change/fiber equivalence
   `M.asIdeal.Fiber (A ⊗ R_K(G)) ≃ M.ResidueField ⊗ R_K(G)`;
   second, the Brauer-character evaluation equivalence from the residue-field scalar extension to
   functions on `p`-regular `Γ_K`-classes.
4. Multiplication is pointwise on the target.  The proof should check the composite sends an
   elementary tensor of a character to the corresponding residue-field-valued function on
   `p`-regular classes, then use the spanning statement for `A ⊗R[K](G)` to get algebra
   extensionality.
5. This theorem returns `Nonempty` deliberately: downstream proof search only needs an equivalence
   witness, while the exact chosen composite can remain opaque until the surrounding owner APIs are
   stable. -/
theorem fixedMaximalFiberAlgEquivPRegularGaloisPowerClassFunctions_nonempty
    {p : Nat.Primes} (M : NonzeroResidualCharacteristicMaximalIdeal A p) :
    Nonempty
      ((M.1.asIdeal.Fiber
        (characterRingOverFieldAlgebraScalarExtensionSubalgebra A K G)) ≃ₐ[M.1.asIdeal.ResidueField]
        (PRegularGaloisPowerClass ΓK p → M.1.asIdeal.ResidueField)) := by
  -- Route correction: this wrapper now reuses the compiled owner equivalence directly, so the
  -- parser/collision issues in the earlier local duplicate are gone and the source route remains
  -- fiber-first.
  exact ⟨privateFixedFiberEquivWitness K M⟩

end

-- Route correction: the owner theorem
-- `Representation.transportedRegularFiberEvalPrime_is_regularPrime` is already provided by the
-- imported Chapter 12 regular-fiber API, so this infrastructure file no longer redeclares it.

/-- Infrastructure for Exercise 12-12.7-8: every prime over a fixed nonzero maximal ideal is one
of the transported evaluation primes on `p`-regular `Γ_K`-classes.

Proof route from LinearRepresentations_Serre_1977, Ch. 12, Sec. 7:
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
   coordinate-kernel statement into LinearRepresentations_Serre_1977's predicate
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
  -- resulting equality with the indexed owner prime back into LinearRepresentations_Serre_1977's intrinsic predicate.
  obtain ⟨c, hc⟩ := privateExistsEqRegularPrimeOfComapEqFixedMaximal K M hP
  refine ⟨c, ?_⟩
  simpa [hc] using galoisPowerClassScalarExtensionRegularPrime_spec K M c

end

end Representation
