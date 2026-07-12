import LinearRepresentations_Serre_1977.Chap12.GaloisPowerClasses

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
private def instFintypeExercise121278ScalarExtensionTransportGroup : Fintype G :=
  Fintype.ofFinite G
attribute [local instance] instFintypeExercise121278ScalarExtensionTransportGroup

local notation "ΓK" => (Representation.exerciseGammaSubgroup (G := G) (L := L) K)
local notation "SpecAKG" =>
  PrimeSpectrum (characterRingOverFieldAlgebraScalarExtensionSubalgebra A K G)

/-- Evaluation on a `Γ_K`-class defines the source-facing map whose kernel is Serre's
zero-residual prime `P₀,c` in `A ⊗ R_K(G)`. -/
def galoisPowerClassScalarExtensionZeroPrimeIdealEval
    (c : GaloisPowerClass ΓK) :
    characterRingOverFieldAlgebraScalarExtensionSubalgebra A K G →+* K :=
  let g : G := Classical.choose ((galoisPowerClassMk_surjective ΓK) c)
  (Pi.evalRingHom (fun _ : G ↦ K) g).comp
    ((characterRingOverFieldAlgebraScalarExtensionSubalgebra A K G).val :
      characterRingOverFieldAlgebraScalarExtensionSubalgebra A K G →+* (G → K))

/-- The prime ideal `P₀,c` of `A ⊗ R_K(G)` obtained by evaluating on the `Γ_K`-class `c`. -/
def galoisPowerClassScalarExtensionZeroPrimeIdeal
    (c : GaloisPowerClass ΓK) : SpecAKG :=
  ⟨RingHom.ker (galoisPowerClassScalarExtensionZeroPrimeIdealEval K c),
    RingHom.ker_isPrime _⟩

variable [IsDomain A] [Ring.HasFiniteQuotients A] [IsFractionRing A K]

/-- Helper for Exercise 12-12.7-8: evaluating the zero-fiber map on a scalar from `A` recovers
its image in the fraction field `K`. -/
lemma galoisPowerClassScalarExtensionZeroPrimeIdealEval_algebraMap
    (c : GaloisPowerClass ΓK) (a : A) :
    galoisPowerClassScalarExtensionZeroPrimeIdealEval K c
      (algebraMap A (characterRingOverFieldAlgebraScalarExtensionSubalgebra A K G) a) =
        algebraMap A K a := by
  change
    (algebraMap A (G → K) a)
      (Classical.choose ((galoisPowerClassMk_surjective ΓK) c)) =
        algebraMap A K a
  rfl

/-- Helper for Exercise 12-12.7-8: the zero-residual prime `P₀,c` contracts to `(0)` in `A`. -/
lemma galoisPowerClassScalarExtensionZeroPrimeIdeal_comap_algebraMap
    (c : GaloisPowerClass ΓK) :
    Ideal.comap
        (algebraMap A (characterRingOverFieldAlgebraScalarExtensionSubalgebra A K G))
        (galoisPowerClassScalarExtensionZeroPrimeIdeal K c).asIdeal = ⊥ := by
  ext a
  change
    galoisPowerClassScalarExtensionZeroPrimeIdealEval K c
        (algebraMap A (characterRingOverFieldAlgebraScalarExtensionSubalgebra A K G) a) = 0 ↔
      a ∈ (⊥ : Ideal A)
  rw [galoisPowerClassScalarExtensionZeroPrimeIdealEval_algebraMap (K := K) c a]
  constructor
  · intro ha
    rw [Ideal.mem_bot]
    apply (IsFractionRing.injective A K)
    simpa using ha
  · intro ha
    rw [Ideal.mem_bot] at ha
    simp [ha]

/-- Helper for Exercise 12-12.7-8: the residue field at `(0)` is another fraction-field model of
`A`. This is the scalar source needed to compare the bottom fiber with `K`-valued evaluation. -/
noncomputable instance botResidueField_isFractionRing :
    IsFractionRing A ((⊥ : Ideal A).ResidueField) := by
  letI : IsFractionRing (A ⧸ (⊥ : Ideal A)) ((⊥ : Ideal A).ResidueField) := inferInstance
  exact IsFractionRing.of_ringEquiv_left (R := A) (S := A ⧸ (⊥ : Ideal A))
    (K := ((⊥ : Ideal A).ResidueField)) (RingEquiv.quotientBot A).symm
    (fun x ↦ by
      change algebraMap A ((⊥ : Ideal A).ResidueField) x =
        algebraMap (A ⧸ (⊥ : Ideal A)) ((⊥ : Ideal A).ResidueField)
          (Ideal.Quotient.mk (⊥ : Ideal A) x)
      rw [Ideal.algebraMap_quotient_residueField_mk])

/-- Helper for Exercise 12-12.7-8: the scalar map `A → K` lifts to the bottom residue field.
This is the coefficient map used in the zero-fiber transport back to `Spec (A ⊗ R_K(G))`. -/
noncomputable instance botResidueField_algebraK :
    Algebra ((⊥ : Ideal A).ResidueField) K :=
  (IsFractionRing.lift (A := A) (K := ((⊥ : Ideal A).ResidueField)) (L := K)
    (g := algebraMap A K) (hg := IsFractionRing.injective A K)).toAlgebra

/-- Helper for Exercise 12-12.7-8: the coefficient maps
`A → ((0).ResidueField) → K` agree with the original scalar map `A → K`. This scalar-tower
instance is the coefficient-side input needed to restrict transported bottom-fiber evaluation
maps from `((0).ResidueField)` back to `A`. -/
instance botResidueField_K_isScalarTower :
    IsScalarTower A ((⊥ : Ideal A).ResidueField) K :=
  IsScalarTower.of_algebraMap_eq fun x ↦ by
    change algebraMap A K x =
      (algebraMap ((⊥ : Ideal A).ResidueField) K)
        (algebraMap A ((⊥ : Ideal A).ResidueField) x)
    exact
      (IsFractionRing.lift_algebraMap
        (A := A) (K := ((⊥ : Ideal A).ResidueField)) (L := K)
        (g := algebraMap A K) (hg := IsFractionRing.injective A K) x).symm

/-- Helper for Exercise 12-12.7-8: the tensor-product owner on `R_K(G)` realizes exactly the
algebra-level scalar extension subalgebra inside `K`-valued functions. -/
noncomputable def tensorCharacterRingOverFieldToSubalgebra
    (F : Type*) [Field F] [Algebra F K] :
    TensorProduct ℤ F (R[K](G)) →ₐ[F]
      characterRingOverFieldAlgebraScalarExtensionSubalgebra F K G :=
  (AlgHom.liftEquiv ℤ F (R[K](G))
      (characterRingOverFieldAlgebraScalarExtensionSubalgebra F K G))
    { toFun := fun χ ↦
        ⟨(χ : G → K),
          mem_characterRingOverFieldAlgebraScalarExtension_of_mem_characterRingOverField
            (A := F) (K := K) (G := G) χ.property⟩
      map_one' := by
        ext g
        rfl
      map_mul' := by
        intro χ ψ
        ext g
        rfl
      map_zero' := by
        ext g
        rfl
      map_add' := by
        intro χ ψ
        ext g
        rfl
      commutes' := by
        intro a
        ext g
        simp }

/-- Helper for Exercise 12-12.7-8: the tensor realization onto the scalar-extension subalgebra is
surjective over every coefficient field mapping to `K`. -/
theorem surjective_tensorCharacterRingOverFieldToSubalgebra
    (F : Type*) [Field F] [Algebra F K] :
    Function.Surjective
      (tensorCharacterRingOverFieldToSubalgebra (K := K) (G := G) F) := by
  intro f
  rcases (R[K](G)).toSubmodule.surjective_tensorToSpan F ⟨(f : G → K), f.2⟩ with ⟨χ, hχ⟩
  refine ⟨χ, ?_⟩
  ext g
  have h :=
    congrArg
      (fun z : Representation.characterRingOverFieldAlgebraScalarExtension F K G ↦ (z : G → K) g)
      hχ
  simpa [tensorCharacterRingOverFieldToSubalgebra] using h

/-- Helper for Exercise 12-12.7-8: over a coefficient field, the tensor realization of `R_K(G)`
into the scalar-extension subalgebra is injective. -/
theorem injective_tensorCharacterRingOverFieldToSubalgebra
    (F : Type*) [Field F] [Algebra F K] [Algebra.IsEpi ℤ F] [Module.Flat ℤ F] :
    Function.Injective
      (tensorCharacterRingOverFieldToSubalgebra (K := K) (G := G) F) := by
  intro χ ψ hχψ
  have hfun :
      ((tensorCharacterRingOverFieldToSubalgebra (K := K) (G := G) F χ :
          characterRingOverFieldAlgebraScalarExtensionSubalgebra F K G) : G → K) =
        ((tensorCharacterRingOverFieldToSubalgebra (K := K) (G := G) F ψ :
          characterRingOverFieldAlgebraScalarExtensionSubalgebra F K G) : G → K) := by
    exact
      congrArg
        (fun f : characterRingOverFieldAlgebraScalarExtensionSubalgebra F K G ↦ (f : G → K))
        hχψ
  have hspan :
      (((R[K](G)).toSubmodule).tensorToSpan F χ :
          Representation.characterRingOverFieldAlgebraScalarExtension F K G) =
        (((R[K](G)).toSubmodule).tensorToSpan F ψ :
          Representation.characterRingOverFieldAlgebraScalarExtension F K G) := by
    ext g
    simpa [tensorCharacterRingOverFieldToSubalgebra] using congrArg (fun f : G → K ↦ f g) hfun
  exact ((R[K](G)).toSubmodule.injective_tensorToSpan F) hspan

/-- Helper for Exercise 12-12.7-8: over any coefficient field mapping to `K`, the tensor-product
owner `F ⊗ R_K(G)` is canonically the scalar-extension subalgebra inside `G → K`. -/
noncomputable def tensorCharacterRingOverFieldAlgEquivSubalgebra
    (F : Type*) [Field F] [Algebra F K] [Algebra.IsEpi ℤ F] [Module.Flat ℤ F] :
    TensorProduct ℤ F (R[K](G)) ≃ₐ[F]
      characterRingOverFieldAlgebraScalarExtensionSubalgebra F K G := by
  let φ := tensorCharacterRingOverFieldToSubalgebra (K := K) (G := G) F
  refine AlgEquiv.ofBijective φ ?_
  exact
    ⟨injective_tensorCharacterRingOverFieldToSubalgebra (K := K) (G := G) F,
      surjective_tensorCharacterRingOverFieldToSubalgebra (K := K) (G := G) F⟩

/-- Helper for Exercise 12-12.7-8: base change along a field extension `A → F` removes the
tensor-associativity bookkeeping from `F ⊗[A] (A ⊗[ℤ] R_K(G))`, leaving the coefficient-changed
tensor owner `F ⊗[ℤ] R_K(G)`. -/
noncomputable def fiber_algEquiv_tensorCharacterRingOverField_baseChange
    (F : Type*) [Field F] [Algebra A F] :
    TensorProduct A F (TensorProduct ℤ A (R[K](G))) ≃ₐ[F] TensorProduct ℤ F (R[K](G)) := by
  let g : ↥R[K](G) ≃ₐ[ℤ] ↥R[K](G) :=
    AlgEquiv.refl (R := ℤ) (A₁ := ↥R[K](G))
  exact
    (Algebra.TensorProduct.assoc ℤ A F F A (R[K](G))).symm.trans
      (Algebra.TensorProduct.congr (Algebra.TensorProduct.rid A F F) g)

/-- Helper for Exercise 12-12.7-8: the tensor-associativity base-change transport above is also
available as an `F`-linear equivalence. This packages the coercion-stable linear endpoint used by
the regular-fiber transport in Serre's source route. -/
noncomputable def fiber_linearEquiv_tensorCharacterRingOverField_baseChange
    (F : Type*) [Field F] [Algebra A F] :
    TensorProduct A F (TensorProduct ℤ A (R[K](G))) ≃ₗ[F] TensorProduct ℤ F (R[K](G)) :=
  (fiber_algEquiv_tensorCharacterRingOverField_baseChange (A := A) (K := K) (G := G) F).toLinearEquiv

/-- Helper for Exercise 12-12.7-8: a prime of `A ⊗ R_K(G)` with zero contraction packages as a
point of the bottom fiber over `(0)`. -/
theorem prime_asIdeal_liesOver_bot
    (𝔭 : SpecAKG)
    (h𝔭 :
      Ideal.comap (algebraMap A (characterRingOverFieldAlgebraScalarExtensionSubalgebra A K G))
        𝔭.asIdeal = ⊥) :
    𝔭.asIdeal.LiesOver (⊥ : Ideal A) := by
  exact ⟨h𝔭.symm⟩

/-- Helper for Exercise 12-12.7-8: a prime of `A ⊗ R_K(G)` with zero contraction yields a prime
of the bottom fiber. -/
noncomputable def prime_over_bot_to_fiber
    (𝔭 : SpecAKG)
    (h𝔭 :
      Ideal.comap (algebraMap A (characterRingOverFieldAlgebraScalarExtensionSubalgebra A K G))
        𝔭.asIdeal = ⊥) :
    PrimeSpectrum
      (((⊥ : Ideal A).Fiber
        (characterRingOverFieldAlgebraScalarExtensionSubalgebra A K G))) :=
  letI : 𝔭.asIdeal.LiesOver (⊥ : Ideal A) :=
    prime_asIdeal_liesOver_bot (A := A) (K := K) (G := G) 𝔭 h𝔭
  PrimeSpectrum.primesOverOrderIsoFiber
    A
    (characterRingOverFieldAlgebraScalarExtensionSubalgebra A K G)
    (⊥ : Ideal A)
    (Ideal.primesOver.mk (⊥ : Ideal A) 𝔭.asIdeal)

/-- Helper for Exercise 12-12.7-8: transporting the packaged bottom-fiber prime back to
`Spec (A ⊗ R_K(G))` recovers the original prime. -/
theorem prime_over_bot_to_fiber_symm
    (𝔭 : SpecAKG)
    (h𝔭 :
      Ideal.comap (algebraMap A (characterRingOverFieldAlgebraScalarExtensionSubalgebra A K G))
        𝔭.asIdeal = ⊥) :
    ((PrimeSpectrum.primesOverOrderIsoFiber
        A
        (characterRingOverFieldAlgebraScalarExtensionSubalgebra A K G)
        (⊥ : Ideal A)).symm
      (prime_over_bot_to_fiber (A := A) (K := K) (G := G) 𝔭 h𝔭)).1 =
        𝔭.asIdeal := by
  letI : 𝔭.asIdeal.LiesOver (⊥ : Ideal A) :=
    prime_asIdeal_liesOver_bot (A := A) (K := K) (G := G) 𝔭 h𝔭
  simpa [prime_over_bot_to_fiber]
    using congrArg PrimeSpectrum.asIdeal
      ((PrimeSpectrum.primesOverOrderIsoFiber
          A
          (characterRingOverFieldAlgebraScalarExtensionSubalgebra A K G)
          (⊥ : Ideal A)).symm_apply_apply
        (Ideal.primesOver.mk (⊥ : Ideal A) 𝔭.asIdeal))

end

end Representation
