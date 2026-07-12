import Mathlib
import StacksProject_2024.Chap10.Definition_10_105_3
import StacksProject_2024.Chap10.Lemma_10_17_2
import StacksProject_2024.Chap10.Lemma_10_155_1
import StacksProject_2024.Chap15.Lemma_15_45_3
import StacksProject_2024.Chap15.Lemma_15_45_5
import StacksProject_2024.Chap15.Lemma_15_107_3
import StacksProject_2024.Chap15.Lemma_15_107_7
import StacksProject_2024.Chap15.Lemma_15_109_2
import StacksProject_2024.Chap15.Lemma_15_109_8
import StacksProject_2024.Chap15.Proposition_15_110_5_Ratliff

-- Declarations for this item will be appended below by the statement pipeline.

universe u

open IsLocalRing TopologicalSpace

section

variable {A : Type u}
variable [CommRing A] [IsLocalRing A] [IsNoetherianRing A]

local notation "ACompletion" => AdicCompletion (maximalIdeal A) A

/- Domain-style sampling:
- primary domain: Noetherian local commutative algebra of geometrically normal formal fibers,
  henselizations, unibranch local rings, and universal catenarity;
- sampled owner declarations:
  `LocalFormalFibersHaveProperty`,
  `branchNumber_eq_one_iff_isUnibranch`,
  `branchNumber_eq_completion_minimalPrimes_of_geometricallyNormal_formalFibers`,
  `universallyCatenaryRing_iff_isFormallyCatenaryRing`;
- best owner abstraction: the source-facing formal-fiber hypothesis belongs to
  `LocalFormalFibersHaveProperty`, while the conclusion should be stated directly in the canonical
  owner `UniversallyCatenaryRing`; the branch-number equalities from Chapter 15 are derived API
  used only as the bridge from the formal-fiber hypothesis to formal catenarity;
- primitive data: the local Noetherian ring `A`, a chosen henselization `Ah`, and the shared
  hypothesis `hgeom`;
- derived API: the universal-catenarity instances for `Ah` and, under `[IsUnibranch A]`, for `A`.

Source/core/bridge triage:
- `source-facing`: the two clauses of Lemma `15.110.6`;
- `core/canonical`: `LocalFormalFibersHaveProperty`, `IsUnibranch`, and
  `UniversallyCatenaryRing`;
- `bridge/view`: the branch-number comparison theorems from `15.107.7` and `15.109.8`, together
  with Ratliff's equivalence `universallyCatenaryRing_iff_isFormallyCatenaryRing`.
-/

/-- Helper for Lemma 15.110.6: if the radical of an ideal is prime, then the corresponding
completion quotient has irreducible, hence equidimensional, prime spectrum. -/
lemma equidimensionalSpace_primeSpectrum_quotient_of_radical_isPrime
    {R : Type u} [CommRing R] (I : Ideal R) (hI : (Ideal.radical I).IsPrime) :
    EquidimensionalSpace (PrimeSpectrum (R ⧸ I)) := by
  letI : (Ideal.radical I).IsPrime := hI
  -- Replace the quotient by `I` with the quotient by `√I`, since they define the same closed set.
  have hzero :
      PrimeSpectrum.zeroLocus (I : Set R) =
        PrimeSpectrum.zeroLocus ((Ideal.radical I : Ideal R) : Set R) := by
    simpa using (PrimeSpectrum.zeroLocus_radical (s := (I : Set R)))
  have hirrRadical : IrreducibleSpace (PrimeSpectrum (R ⧸ Ideal.radical I)) := by
    -- The quotient by a prime ideal is a domain, so its prime spectrum is irreducible.
    letI : IsDomain (R ⧸ Ideal.radical I) := Ideal.Quotient.isDomain (Ideal.radical I)
    rw [PrimeSpectrum.irreducibleSpace_iff_isPrime_nilradical]
    simpa [nilradical_eq_zero (R := R ⧸ Ideal.radical I)]
      using (show (⊥ : Ideal (R ⧸ Ideal.radical I)).IsPrime by infer_instance)
  have hirrZero :
      IrreducibleSpace
        (PrimeSpectrum.zeroLocus ((Ideal.radical I : Ideal R) : Set R)) := by
    -- Transport irreducibility across the standard quotient-spectrum homeomorphism.
    exact
      (Ideal.primeSpectrum_quotient_homeomorph_zeroLocus (Ideal.radical I)).isHomeomorph
        .irreducibleSpace_iff.mp hirrRadical
  have hirrQuot : IrreducibleSpace (PrimeSpectrum (R ⧸ I)) := by
    -- Now move back from `V(√I) = V(I)` to the original quotient.
    exact
      (Ideal.primeSpectrum_quotient_homeomorph_zeroLocus I).isHomeomorph.irreducibleSpace_iff.mpr
        (hzero ▸ hirrZero)
  letI : IrreducibleSpace (PrimeSpectrum (R ⧸ I)) := hirrQuot
  infer_instance

/-- Helper for Lemma 15.110.6: in a unibranch local ring, the nilradical is the unique minimal
prime. -/
lemma minimalPrimes_eq_singleton_nilradical_of_isUnibranch [IsUnibranch A] :
    minimalPrimes A = {nilradical A} := by
  letI : (nilradical A).IsPrime := by
    -- The reduction of a unibranch ring is a domain, so the nilradical quotient is prime.
    simpa [unibranchReduction] using
      (Ideal.Quotient.isDomain_iff_prime (R := A) (I := nilradical A)).mp inferInstance
  -- Once the nilradical is prime, it is the unique minimal prime of `A`.
  simpa [minimalPrimes, nilradical] using
    (show (nilradical A).minimalPrimes = {nilradical A} from
      Ideal.minimalPrimes_eq_subsingleton_self)

/-- Helper for Lemma 15.110.6: geometrically normal formal fibers and unibranchness force formal
catenarity by making the completed quotient over the unique minimal prime irreducible. -/
lemma isFormallyCatenaryRing_of_unibranch_of_geometricallyNormal_formalFibers
    [IsUnibranch A]
    (hgeom : LocalFormalFibersHaveProperty Algebra.IsGeometricallyNormalProperty A) :
    IsFormallyCatenaryRing A := by
  -- Choose a henselization so the source branch-count comparison can be applied verbatim.
  obtain ⟨Ah, _, _, _⟩ := exists_henselization A
  let _ : IsNoetherianRing Ah := isNoetherianRing_henselization A Ah
  have hminimalA : minimalPrimes A = {nilradical A} :=
    minimalPrimes_eq_singleton_nilradical_of_isUnibranch (A := A)
  letI : (nilradical A).IsPrime := by
    -- Reuse the singleton-minimal-prime description to keep the target proof on the nilradical.
    simpa [hminimalA, minimalPrimes, nilradical] using
      (show (nilradical A).IsPrime by
        simpa [unibranchReduction] using
          (Ideal.Quotient.isDomain_iff_prime (R := A) (I := nilradical A)).mp inferInstance)
  have hp : nilradical A ∈ minimalPrimes A := by
    rw [hminimalA]
    simp
  let p : minimalPrimes A := ⟨nilradical A, hp⟩
  have hcount :
      branchNumber A Ah = (minimalPrimes ACompletion).encard :=
    branchNumber_eq_completion_minimalPrimes_of_geometricallyNormal_formalFibers
      (A := A) (Ah := Ah) hgeom
  have hprime_all :
      ∀ q : minimalPrimes Ah,
        (Ideal.radical (Ideal.map (henselizationCompletionComparison A Ah) q)).IsPrime :=
    (branchNumber_eq_completion_minimalPrimes_iff_radical_map_minimalPrime_isPrime
      (A := A) (Ah := Ah)).mp hcount
  have hminimalAh_unique :
      ∃! q : Ideal Ah, q ∈ minimalPrimes Ah :=
    (isUnibranch_iff_existsUnique_minimalPrime_henselization (A := A) (Ah := Ah)).mp inferInstance
  have hminimalAh : minimalPrimes Ah = {nilradical Ah} := by
    rcases hminimalAh_unique with ⟨q, hq, hq_unique⟩
    have hnil : nilradical Ah = q := by
      rw [← Ideal.sInf_minimalPrimes]
      ext x
      simp [hq_unique]
    ext J
    constructor
    · intro hJ
      rw [hnil]
      simpa using hq_unique J hJ
    · rintro hJ
      rw [Set.mem_singleton_iff] at hJ
      rwa [hJ]
  have hq : nilradical Ah ∈ minimalPrimes Ah := by
    rw [hminimalAh]
    simp
  let q : minimalPrimes Ah := ⟨nilradical Ah, hq⟩
  have hmap_nil :
      Ideal.map (algebraMap A Ah) (nilradical A) = nilradical Ah :=
    henselization_map_nilradical (R := A) (Rh := Ah)
  have hradical_eq :
      Ideal.radical (Ideal.map (henselizationCompletionComparison A Ah) q.1) =
        Ideal.radical (Ideal.map (algebraMap A ACompletion) p.1) := by
    -- Rewrite the unique henselization minimal prime as the image of the source nilradical.
    calc
      Ideal.radical (Ideal.map (henselizationCompletionComparison A Ah) q.1) =
          Ideal.radical
            (Ideal.map (henselizationCompletionComparison A Ah)
              (Ideal.map (algebraMap A Ah) p.1)) := by
            rw [show q.1 = Ideal.map (algebraMap A Ah) p.1 by simpa [p] using hmap_nil.symm]
      _ = Ideal.radical
          (Ideal.map ((henselizationCompletionComparison A Ah).comp (algebraMap A Ah)) p.1) := by
            rw [Ideal.map_map]
      _ = Ideal.radical (Ideal.map (algebraMap A ACompletion) p.1) := by
            congr 1
            ext x
            rfl
  have hprime_p :
      (Ideal.radical (Ideal.map (algebraMap A ACompletion) p.1)).IsPrime := by
    -- The branch-count criterion now applies to the unique source minimal prime.
    rw [← hradical_eq]
    exact hprime_all q
  refine
    { toIsLocalRing := inferInstance
      toIsNoetherianRing := inferInstance
      equidimensional_completion_quotient := fun p' ↦ ?_ }
  have hp' : p' = p := by
    apply Subtype.ext
    simpa [hminimalA] using p'.2
  subst hp'
  -- The formal-catenary quotient is equidimensional because its radical is prime.
  exact
    equidimensionalSpace_primeSpectrum_quotient_of_radical_isPrime
      (R := ACompletion) (I := Ideal.map (algebraMap A ACompletion) p.1) hprime_p

-- Proof sketch: apply the branch-count comparison from Lemma `15.109.8` and the radical-primality
-- criterion from Lemma `15.109.2` to each minimal prime of `Ah`, obtaining the equidimensional
-- completion quotients required for formal catenarity. Ratliff's equivalence then upgrades formal
-- catenarity of `Ah` to universal catenarity.
/-- Lemma 15.110.6 (1): if the Noetherian local ring `A` has geometrically normal formal fibers,
then any chosen henselization `Ah` of `A` is universally catenary. -/
theorem universallyCatenaryRing_henselization_of_geometricallyNormal_formalFibers
    {Ah : Type u} [CommRing Ah] [Algebra A Ah] [IsHenselizationOf A Ah]
    (hgeom : LocalFormalFibersHaveProperty Algebra.IsGeometricallyNormalProperty A) :
    UniversallyCatenaryRing Ah := by
  -- TODO: transport the prime-radical quotients from the common completion `A^∧` to the
  -- maximal-ideal completion of `Ah` using the canonical completion comparison
  -- `A^∧ ≃ (A^h)^∧`; the remaining blocker is the corresponding quotient-level ideal identity.
  sorry

-- Proof sketch: under `[IsUnibranch A]`, Lemma `15.107.7` gives `branchNumber A Ah = 1`. Combine
-- this with the branch-count formula from Lemma `15.109.8` to force each completed quotient by a
-- minimal prime of `A` to have a unique minimal prime, hence to be equidimensional. Ratliff's
-- equivalence then yields universal catenarity of `A`.
/-- Lemma 15.110.6 (2): if the Noetherian local ring `A` has geometrically normal formal fibers
and `A` is unibranch, then `A` is universally catenary. In particular this applies to normal local
rings. -/
theorem universallyCatenaryRing_of_unibranch_of_geometricallyNormal_formalFibers
    [IsUnibranch A]
    (hgeom : LocalFormalFibersHaveProperty Algebra.IsGeometricallyNormalProperty A) :
    UniversallyCatenaryRing A := by
  -- Build formal catenarity first, then invoke Ratliff's equivalence only at the end.
  exact
    (universallyCatenaryRing_iff_isFormallyCatenaryRing A).mpr
      (isFormallyCatenaryRing_of_unibranch_of_geometricallyNormal_formalFibers
        (A := A) hgeom)

end
