import LinearRepresentations_Serre_1977.Chap12.Exercise_12_12_7_8.RegularPrimeTensorOwner

open scoped Representation

noncomputable section

universe u v w

namespace Representation

section

variable {G : Type w} [Group G] [Finite G]
variable {A : Type v} [CommRing A]
variable {L : Type w} [Field L] [NumberField L]
variable [IsCyclotomicExtension {Monoid.exponent G} ℚ L]

variable (K : IntermediateField ℚ L)
variable [Algebra A K]

/-- Helper for Exercise 12-12.7-8: a private `Fintype` witness for the finite group `G`. -/
private def instFintypeExercise121278RegularPrimeClassificationGroup : Fintype G :=
  Fintype.ofFinite G
attribute [local instance] instFintypeExercise121278RegularPrimeClassificationGroup

local notation "ΓK" => (Representation.exerciseGammaSubgroup (G := G) (L := L) K)
local notation "SpecAKG" =>
  PrimeSpectrum (characterRingOverFieldAlgebraScalarExtensionSubalgebra A K G)

variable [IsDomain A] [Ring.HasFiniteQuotients A] [IsFractionRing A K]

section RegularPrime

variable {p : Nat.Primes}

/-- Helper for Exercise 12-12.7-8: once a prime over `M` has Serre's defining residue test for
the fixed class `c`, it already satisfies the regular-prime predicate. -/
theorem transportedRegularFiberEvalPrime_is_regularPrime
    (M : NonzeroResidualCharacteristicMaximalIdeal A p)
    (c : PRegularGaloisPowerClass ΓK p)
    (P : SpecAKG)
    (hfiber : P.asIdeal.LiesOver M.1.asIdeal)
    (heval :
      ∀ f : characterRingOverFieldAlgebraScalarExtensionSubalgebra A K G,
        f ∈ P.asIdeal ↔
          ∀ x : { x : G // IsPRegular p x },
            pRegularGaloisPowerClassMk ΓK p x = c →
              ∃ a : M.1.asIdeal, algebraMap A K a.1 = (f : G → K) x.1) :
    IsGaloisPowerClassScalarExtensionRegularPrime K M c P := by
  exact ⟨hfiber.over.symm, heval⟩

/-- Helper for Exercise 12-12.7-8: for fixed `(M, c)`, Serre's intrinsic predicate determines at
most one prime of `A ⊗ R_K(G)`. -/
theorem eq_of_isGaloisPowerClassScalarExtensionRegularPrime
    (M : NonzeroResidualCharacteristicMaximalIdeal A p)
    (c : PRegularGaloisPowerClass ΓK p)
    {P Q : SpecAKG}
    (hP : IsGaloisPowerClassScalarExtensionRegularPrime K M c P)
    (hQ : IsGaloisPowerClassScalarExtensionRegularPrime K M c Q) :
    P = Q := by
  apply PrimeSpectrum.ext
  ext f
  exact (hP.2 f).trans (hQ.2 f).symm

/-- Helper for Exercise 12-12.7-8: transporting a prime of the regular fiber over `M` back
through `PrimeSpectrum.primesOverOrderIsoFiber` gives the corresponding ambient prime of
`A ⊗ R_K(G)`. -/
theorem prime_asIdeal_liesOver_fixed_maximal
    (M : NonzeroResidualCharacteristicMaximalIdeal A p)
    (𝔭 : SpecAKG)
    (h𝔭 :
      Ideal.comap (algebraMap A (characterRingOverFieldAlgebraScalarExtensionSubalgebra A K G))
        𝔭.asIdeal = M.1.asIdeal) :
    𝔭.asIdeal.LiesOver M.1.asIdeal := by
  exact ⟨h𝔭.symm⟩

/-- Helper for Exercise 12-12.7-8: a prime of `A ⊗ R_K(G)` lying over `M` gives a prime of the
fiber over `M`. -/
noncomputable def prime_over_fixed_maximal_to_fiber
    (M : NonzeroResidualCharacteristicMaximalIdeal A p)
    (𝔭 : SpecAKG)
    (h𝔭 :
      Ideal.comap (algebraMap A (characterRingOverFieldAlgebraScalarExtensionSubalgebra A K G))
        𝔭.asIdeal = M.1.asIdeal) :
    PrimeSpectrum
      (M.1.asIdeal.Fiber
        (characterRingOverFieldAlgebraScalarExtensionSubalgebra A K G)) :=
  letI : 𝔭.asIdeal.LiesOver M.1.asIdeal :=
    prime_asIdeal_liesOver_fixed_maximal (A := A) (K := K) (G := G) M 𝔭 h𝔭
  PrimeSpectrum.primesOverOrderIsoFiber
    A
    (characterRingOverFieldAlgebraScalarExtensionSubalgebra A K G)
    M.1.asIdeal
    (Ideal.primesOver.mk M.1.asIdeal 𝔭.asIdeal)

/-- Helper for Exercise 12-12.7-8: transporting the packaged fiber prime back from the fiber over
`M` recovers the original ambient prime. -/
theorem prime_over_fixed_maximal_to_fiber_symm
    (M : NonzeroResidualCharacteristicMaximalIdeal A p)
    (𝔭 : SpecAKG)
    (h𝔭 :
      Ideal.comap (algebraMap A (characterRingOverFieldAlgebraScalarExtensionSubalgebra A K G))
        𝔭.asIdeal = M.1.asIdeal) :
    ((PrimeSpectrum.primesOverOrderIsoFiber
        A
        (characterRingOverFieldAlgebraScalarExtensionSubalgebra A K G)
        M.1.asIdeal).symm
      (prime_over_fixed_maximal_to_fiber (A := A) (K := K) (G := G) M 𝔭 h𝔭)).1 =
        𝔭.asIdeal := by
  letI : 𝔭.asIdeal.LiesOver M.1.asIdeal :=
    prime_asIdeal_liesOver_fixed_maximal (A := A) (K := K) (G := G) M 𝔭 h𝔭
  simpa [prime_over_fixed_maximal_to_fiber]
    using congrArg PrimeSpectrum.asIdeal
      ((PrimeSpectrum.primesOverOrderIsoFiber
          A
          (characterRingOverFieldAlgebraScalarExtensionSubalgebra A K G)
          M.1.asIdeal).symm_apply_apply
        (Ideal.primesOver.mk M.1.asIdeal 𝔭.asIdeal))

noncomputable def regular_fiber_prime_to_specAKG
    (M : NonzeroResidualCharacteristicMaximalIdeal A p)
    (q :
      PrimeSpectrum
        (M.1.asIdeal.Fiber
          (characterRingOverFieldAlgebraScalarExtensionSubalgebra A K G))) :
    SpecAKG :=
  ⟨((PrimeSpectrum.primesOverOrderIsoFiber
      A
      (characterRingOverFieldAlgebraScalarExtensionSubalgebra A K G)
      M.1.asIdeal).symm q).1,
    inferInstance⟩

/-- Helper for Exercise 12-12.7-8: the transport from regular-fiber primes to ambient primes over
the fixed maximal ideal `M` is injective. -/
theorem regular_fiber_prime_to_specAKG_injective
    (M : NonzeroResidualCharacteristicMaximalIdeal A p) :
    Function.Injective
      (regular_fiber_prime_to_specAKG (A := A) (K := K) (G := G) M) := by
  intro q₁ q₂ hq
  have hsub :
      (PrimeSpectrum.primesOverOrderIsoFiber
          A
          (characterRingOverFieldAlgebraScalarExtensionSubalgebra A K G)
          M.1.asIdeal).symm q₁ =
        (PrimeSpectrum.primesOverOrderIsoFiber
          A
          (characterRingOverFieldAlgebraScalarExtensionSubalgebra A K G)
          M.1.asIdeal).symm q₂ := by
    apply Subtype.ext
    simpa [regular_fiber_prime_to_specAKG] using congrArg PrimeSpectrum.asIdeal hq
  exact
    (PrimeSpectrum.primesOverOrderIsoFiber
      A
      (characterRingOverFieldAlgebraScalarExtensionSubalgebra A K G)
      M.1.asIdeal).symm.injective hsub

/-- Helper for Exercise 12-12.7-8: sending an ambient prime over `M` into the fiber and
transporting it back along `regular_fiber_prime_to_specAKG` returns the original prime. -/
theorem regular_fiber_prime_to_specAKG_prime_over_fixed_maximal_to_fiber
    (M : NonzeroResidualCharacteristicMaximalIdeal A p)
    (𝔭 : SpecAKG)
    (h𝔭 :
      Ideal.comap (algebraMap A (characterRingOverFieldAlgebraScalarExtensionSubalgebra A K G))
        𝔭.asIdeal = M.1.asIdeal) :
    regular_fiber_prime_to_specAKG (A := A) (K := K) (G := G) M
        (prime_over_fixed_maximal_to_fiber (A := A) (K := K) (G := G) M 𝔭 h𝔭) =
      𝔭 := by
  apply PrimeSpectrum.ext
  simpa [regular_fiber_prime_to_specAKG] using
    prime_over_fixed_maximal_to_fiber_symm (A := A) (K := K) (G := G) M 𝔭 h𝔭

/-- Helper for Exercise 12-12.7-8: every prime of a finite product of fields indexed by
`p`-regular `Γ_K`-classes is a coordinate-evaluation prime. -/
theorem exists_eq_comap_evalRingHom_bot_of_primeSpectrum_pRegularGaloisPowerClass
    (M : NonzeroResidualCharacteristicMaximalIdeal A p)
    (P : PrimeSpectrum (PRegularGaloisPowerClass ΓK p → M.1.asIdeal.ResidueField)) :
    ∃ c : PRegularGaloisPowerClass ΓK p,
      PrimeSpectrum.comap
          (Pi.evalRingHom
            (fun _ : PRegularGaloisPowerClass ΓK p ↦ M.1.asIdeal.ResidueField) c)
          ⟨(⊥ : Ideal M.1.asIdeal.ResidueField), inferInstance⟩ = P := by
  obtain ⟨c, q, hq⟩ :=
    PrimeSpectrum.exists_comap_evalRingHom_eq
      (R := fun _ : PRegularGaloisPowerClass ΓK p ↦ M.1.asIdeal.ResidueField) P
  refine ⟨c, ?_⟩
  have hqbotIdeal : q.asIdeal = ⊥ := by
    exact Ideal.eq_bot_of_prime q.asIdeal
  have hqbot : q = ⟨(⊥ : Ideal M.1.asIdeal.ResidueField), inferInstance⟩ := by
    apply PrimeSpectrum.ext
    simpa using hqbotIdeal
  simpa [hqbot] using hq

/-- Helper for Exercise 12-12.7-8: the coordinate-evaluation prime in the function ring on
`p`-regular `Γ_K`-classes over the residue field of `M`. -/
noncomputable def regular_fiber_eval_prime
    (M : NonzeroResidualCharacteristicMaximalIdeal A p)
    (c : PRegularGaloisPowerClass ΓK p) :
    PrimeSpectrum (PRegularGaloisPowerClass ΓK p → M.1.asIdeal.ResidueField) :=
  PrimeSpectrum.comap
    (Pi.evalRingHom (fun _ : PRegularGaloisPowerClass ΓK p ↦ M.1.asIdeal.ResidueField) c)
    ⟨(⊥ : Ideal M.1.asIdeal.ResidueField), inferInstance⟩

/-- Helper for Exercise 12-12.7-8: distinct `p`-regular `Γ_K`-classes define distinct
coordinate-evaluation primes in the regular-fiber function ring. -/
theorem regular_fiber_eval_prime_eq_iff
    (M : NonzeroResidualCharacteristicMaximalIdeal A p)
    (c₁ c₂ : PRegularGaloisPowerClass ΓK p) :
    regular_fiber_eval_prime (A := A) (K := K) (G := G) M c₁ =
        regular_fiber_eval_prime (A := A) (K := K) (G := G) M c₂ ↔
      c₁ = c₂ := by
  constructor
  · intro hprime
    by_contra hne
    classical
    let f : PRegularGaloisPowerClass ΓK p → M.1.asIdeal.ResidueField :=
      fun d ↦ if d = c₁ then 1 else 0
    have hne' : c₂ ≠ c₁ := fun h ↦ hne h.symm
    have hf₂ : f ∈ (regular_fiber_eval_prime (A := A) (K := K) (G := G) M c₂).asIdeal := by
      change f c₂ = 0
      simpa [f] using hne'
    have hf₁ : f ∉ (regular_fiber_eval_prime (A := A) (K := K) (G := G) M c₁).asIdeal := by
      change f c₁ ≠ 0
      simp [f]
    exact hf₁ (by simpa [hprime] using hf₂)
  · intro hc
    subst hc
    rfl

/-- Helper for Exercise 12-12.7-8: an algebra equivalence from the fixed fiber over `M` to the
function ring on `p`-regular `Γ_K`-classes transports coordinate-evaluation primes back to the
fiber. -/
noncomputable def regular_fiber_lift
    (M : NonzeroResidualCharacteristicMaximalIdeal A p)
    (e : (M.1.asIdeal.Fiber
      (characterRingOverFieldAlgebraScalarExtensionSubalgebra A K G)) ≃ₐ[M.1.asIdeal.ResidueField]
        (PRegularGaloisPowerClass ΓK p → M.1.asIdeal.ResidueField))
    (c : PRegularGaloisPowerClass ΓK p) :
    PrimeSpectrum
      (M.1.asIdeal.Fiber
        (characterRingOverFieldAlgebraScalarExtensionSubalgebra A K G)) :=
  (PrimeSpectrum.comapEquiv e.toRingEquiv).symm
    (regular_fiber_eval_prime (A := A) (K := K) (G := G) M c)

/-- Helper for Exercise 12-12.7-8: once the fixed fiber over `M` is identified with the function
ring on `p`-regular `Γ_K`-classes, every prime of that fiber is the lift of a
coordinate-evaluation prime. -/
theorem regular_fiber_lift_surjective
    (M : NonzeroResidualCharacteristicMaximalIdeal A p)
    (e : (M.1.asIdeal.Fiber
      (characterRingOverFieldAlgebraScalarExtensionSubalgebra A K G)) ≃ₐ[M.1.asIdeal.ResidueField]
        (PRegularGaloisPowerClass ΓK p → M.1.asIdeal.ResidueField)) :
    Function.Surjective (regular_fiber_lift (A := A) (K := K) (G := G) M e) := by
  intro q
  let E :
      PrimeSpectrum (PRegularGaloisPowerClass ΓK p → M.1.asIdeal.ResidueField) ≃o
        PrimeSpectrum
          (M.1.asIdeal.Fiber
            (characterRingOverFieldAlgebraScalarExtensionSubalgebra A K G)) :=
    (PrimeSpectrum.comapEquiv
      (R := M.1.asIdeal.Fiber
        (characterRingOverFieldAlgebraScalarExtensionSubalgebra A K G))
      (S := PRegularGaloisPowerClass ΓK p → M.1.asIdeal.ResidueField)
      e.toRingEquiv).symm
  obtain ⟨c, hc⟩ :=
    exists_eq_comap_evalRingHom_bot_of_primeSpectrum_pRegularGaloisPowerClass
      (A := A) (K := K) (G := G) M (E.symm q)
  refine ⟨c, ?_⟩
  calc
    regular_fiber_lift (A := A) (K := K) (G := G) M e c
        = E (regular_fiber_eval_prime (A := A) (K := K) (G := G) M c) := by
            rfl
    _ = E (E.symm q) := by
          simpa [E, regular_fiber_eval_prime] using congrArg E hc
    _ = q := by
          simpa [E] using E.apply_symm_apply q

/-- Helper for Exercise 12-12.7-8: after transporting the fixed fiber over `M` to the
`p`-regular function ring, equality of lifted coordinate primes is equivalent to equality of the
underlying `p`-regular `Γ_K`-classes. -/
theorem regular_fiber_lift_eq_iff
    (M : NonzeroResidualCharacteristicMaximalIdeal A p)
    (e : (M.1.asIdeal.Fiber
      (characterRingOverFieldAlgebraScalarExtensionSubalgebra A K G)) ≃ₐ[M.1.asIdeal.ResidueField]
        (PRegularGaloisPowerClass ΓK p → M.1.asIdeal.ResidueField))
    (c₁ c₂ : PRegularGaloisPowerClass ΓK p) :
    regular_fiber_lift (A := A) (K := K) (G := G) M e c₁ =
        regular_fiber_lift (A := A) (K := K) (G := G) M e c₂ ↔
      c₁ = c₂ := by
  let E :
      PrimeSpectrum (PRegularGaloisPowerClass ΓK p → M.1.asIdeal.ResidueField) ≃o
        PrimeSpectrum
          (M.1.asIdeal.Fiber
            (characterRingOverFieldAlgebraScalarExtensionSubalgebra A K G)) :=
    (PrimeSpectrum.comapEquiv
      (R := M.1.asIdeal.Fiber
        (characterRingOverFieldAlgebraScalarExtensionSubalgebra A K G))
      (S := PRegularGaloisPowerClass ΓK p → M.1.asIdeal.ResidueField)
      e.toRingEquiv).symm
  constructor
  · intro hlift
    have heval :
        regular_fiber_eval_prime (A := A) (K := K) (G := G) M c₁ =
          regular_fiber_eval_prime (A := A) (K := K) (G := G) M c₂ := by
      exact E.injective <| by simpa [regular_fiber_lift, E] using hlift
    exact (regular_fiber_eval_prime_eq_iff (A := A) (K := K) (G := G) M c₁ c₂).mp heval
  · intro hc
    subst hc
    rfl

/-- Helper for Exercise 12-12.7-8: after identifying the fixed fiber over `M` with the function
ring on `p`-regular `Γ_K`-classes, the coordinate-evaluation prime at `c` transports to an
ambient prime of `A ⊗ R_K(G)`. -/
noncomputable def regular_fiber_coordinate_prime
    (M : NonzeroResidualCharacteristicMaximalIdeal A p)
    (e : (M.1.asIdeal.Fiber
      (characterRingOverFieldAlgebraScalarExtensionSubalgebra A K G)) ≃ₐ[M.1.asIdeal.ResidueField]
        (PRegularGaloisPowerClass ΓK p → M.1.asIdeal.ResidueField))
    (c : PRegularGaloisPowerClass ΓK p) :
    SpecAKG :=
  regular_fiber_prime_to_specAKG (A := A) (K := K) (G := G) M
    (regular_fiber_lift (A := A) (K := K) (G := G) M e c)

/-- Helper for Exercise 12-12.7-8: once the fixed fiber is identified with the function ring on
`p`-regular `Γ_K`-classes, the remaining classification of primes over `M` is purely
prime-spectrum transport. -/
theorem regular_fiber_prime_classification_package_of_algEquiv
    (M : NonzeroResidualCharacteristicMaximalIdeal A p)
    (e : (M.1.asIdeal.Fiber
      (characterRingOverFieldAlgebraScalarExtensionSubalgebra A K G)) ≃ₐ[M.1.asIdeal.ResidueField]
        (PRegularGaloisPowerClass ΓK p → M.1.asIdeal.ResidueField))
    (hcoordinate : ∀ c : PRegularGaloisPowerClass ΓK p,
      IsGaloisPowerClassScalarExtensionRegularPrime K M c
        (regular_fiber_coordinate_prime (A := A) (K := K) (G := G) M e c))
    (htransport : ∀ {𝔭 : SpecAKG} {c : PRegularGaloisPowerClass ΓK p}
      (h𝔭 :
        Ideal.comap
            (algebraMap A (characterRingOverFieldAlgebraScalarExtensionSubalgebra A K G))
            𝔭.asIdeal = M.1.asIdeal),
      IsGaloisPowerClassScalarExtensionRegularPrime K M c 𝔭 →
        prime_over_fixed_maximal_to_fiber (A := A) (K := K) (G := G) M 𝔭 h𝔭 =
          regular_fiber_lift (A := A) (K := K) (G := G) M e c) :
    (∀ c : PRegularGaloisPowerClass ΓK p,
      ∃! P : SpecAKG, IsGaloisPowerClassScalarExtensionRegularPrime K M c P) ∧
    (∀ {𝔭 : SpecAKG},
      Ideal.comap (algebraMap A (characterRingOverFieldAlgebraScalarExtensionSubalgebra A K G))
        𝔭.asIdeal = M.1.asIdeal →
        ∃ c : PRegularGaloisPowerClass ΓK p,
          IsGaloisPowerClassScalarExtensionRegularPrime K M c 𝔭) := by
  refine ⟨?_, ?_⟩
  · intro c
    refine
      ⟨regular_fiber_coordinate_prime (A := A) (K := K) (G := G) M e c, hcoordinate c, ?_⟩
    intro P hP
    have hPfiber :
        prime_over_fixed_maximal_to_fiber (A := A) (K := K) (G := G) M P hP.1 =
          regular_fiber_lift (A := A) (K := K) (G := G) M e c :=
      htransport hP.1 hP
    calc
      P =
          regular_fiber_prime_to_specAKG (A := A) (K := K) (G := G) M
            (prime_over_fixed_maximal_to_fiber (A := A) (K := K) (G := G) M P hP.1) := by
              symm
              exact
                regular_fiber_prime_to_specAKG_prime_over_fixed_maximal_to_fiber
                  (A := A) (K := K) (G := G) M P hP.1
      _ = regular_fiber_coordinate_prime (A := A) (K := K) (G := G) M e c := by
            simpa [regular_fiber_coordinate_prime, hPfiber]
  · intro 𝔭 h𝔭
    let q :=
      prime_over_fixed_maximal_to_fiber (A := A) (K := K) (G := G) M 𝔭 h𝔭
    obtain ⟨c, hc⟩ :=
      regular_fiber_lift_surjective (A := A) (K := K) (G := G) M e q
    have hambient :
        regular_fiber_coordinate_prime (A := A) (K := K) (G := G) M e c = 𝔭 := by
      calc
        regular_fiber_coordinate_prime (A := A) (K := K) (G := G) M e c
            = regular_fiber_prime_to_specAKG (A := A) (K := K) (G := G) M q := by
                simpa [regular_fiber_coordinate_prime, q] using
                  congrArg
                    (regular_fiber_prime_to_specAKG (A := A) (K := K) (G := G) M)
                    hc
        _ = 𝔭 := by
              simpa [q] using
                regular_fiber_prime_to_specAKG_prime_over_fixed_maximal_to_fiber
                  (A := A) (K := K) (G := G) M 𝔭 h𝔭
    refine ⟨c, ?_⟩
    simpa [hambient] using hcoordinate c

/-- Helper for Exercise 12-12.7-8: once primes of the fixed fiber over `M` are classified by
`p`-regular `Γ_K`-classes, the same classification transports back to ambient primes over `M`. -/
theorem exists_isGaloisPowerClassScalarExtensionRegularPrime_of_comap_eq_fixed_maximal_of_regularFiberClassification
    (M : NonzeroResidualCharacteristicMaximalIdeal A p)
    (hclass :
      ∀ q :
        PrimeSpectrum
          (M.1.asIdeal.Fiber
            (characterRingOverFieldAlgebraScalarExtensionSubalgebra A K G)),
        ∃ c : PRegularGaloisPowerClass ΓK p,
          IsGaloisPowerClassScalarExtensionRegularPrime K M c
            (regular_fiber_prime_to_specAKG (A := A) (K := K) (G := G) M q))
    {𝔭 : SpecAKG}
    (h𝔭 :
      Ideal.comap (algebraMap A (characterRingOverFieldAlgebraScalarExtensionSubalgebra A K G))
        𝔭.asIdeal = M.1.asIdeal) :
    ∃ c : PRegularGaloisPowerClass ΓK p,
      IsGaloisPowerClassScalarExtensionRegularPrime K M c 𝔭 := by
  let q :=
    prime_over_fixed_maximal_to_fiber (A := A) (K := K) (G := G) M 𝔭 h𝔭
  obtain ⟨c, hc⟩ := hclass q
  refine ⟨c, ?_⟩
  have hq :
      regular_fiber_prime_to_specAKG (A := A) (K := K) (G := G) M q = 𝔭 := by
    simpa [q] using
      regular_fiber_prime_to_specAKG_prime_over_fixed_maximal_to_fiber
        (A := A) (K := K) (G := G) M 𝔭 h𝔭
  simpa [hq] using hc

end RegularPrime

end

end Representation
