import Mathlib
import StacksProject_2024.stacks_project.Chap10.Definition_10_110_7
import StacksProject_2024.stacks_project.Chap10.Lemma_10_105_5
import StacksProject_2024.stacks_project.Chap10.Lemma_10_105_9
import StacksProject_2024.stacks_project.Chap10.Remark_10_160_9
import StacksProject_2024.stacks_project.Chap15.Definition_15_52_1
import StacksProject_2024.stacks_project.Chap15.Proposition_15_48_7
import StacksProject_2024.stacks_project.Chap15.Proposition_15_50_12

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

/- Domain-style sampling:
- primary domain: excellence in commutative algebra, owned by the chapter class
  `IsExcellentRing`.
- sampled owner declarations of the same kind:
  `IsExcellentRing`,
  `IsQuasiExcellentRing`,
  `isGRing_of_finiteType`,
  `isJ2Ring_of_finiteType`,
  `universallyCatenaryRing_of_cohenMacaulayRing`,
  `universallyCatenaryRing_of_isCompleteLocalRing`,
  `universallyCatenaryRing_of_essFiniteType`.
- best owner abstraction: `IsExcellentRing`.
- primitive data vs. derived API:
  the primitive data for excellence are exactly the upstream owner components
  `IsGRing`, `IsJ2Ring`, and `UniversallyCatenaryRing`;
  the field, complete-local, Dedekind, and finite-type clauses below should therefore build
  `IsExcellentRing` directly from those owners, while the special case `ℤ` should be recorded by
  direct recall instead of a parallel wrapper instance.

Source/core/bridge triage:
- `source-facing`: the concrete excellence sources listed in Proposition `15.52.3`;
- `core/canonical`: the owner classes `IsExcellentRing`, `IsQuasiExcellentRing`,
  `IsGRing`, `IsJ2Ring`, and `UniversallyCatenaryRing`;
- `bridge/view`: the regular/Cohen-Macaulay-to-universal-catenarity bridge, the complete-local
  universal-catenarity theorem, and the finite-type permanence theorems for the component owners.
-/

section

variable (K : Type u) [Field K]

-- Proof sketch: Proposition `15.50.12` shows that a field is a `G`-ring, and
-- Proposition `15.48.7` shows that it is `J-2`. Fields are universally catenary because fields
-- are regular, hence Cohen-Macaulay, and Lemma `10.105.9` implies that Noetherian
-- Cohen-Macaulay rings are universally catenary.
/-- Proposition 15.52.3 (1): fields are excellent. -/
instance field_isExcellentRing : IsExcellentRing K := by
  letI : IsQuasiExcellentRing K := IsQuasiExcellentRing.mk
  let hUC : UniversallyCatenaryRing K :=
    universallyCatenaryRing_of_cohenMacaulayRing inferInstance
  letI : UniversallyCatenaryRing K := hUC
  exact IsExcellentRing.mk hUC.catenary_of_finiteType

end

section

variable (R : Type u) [CommRing R] [IsNoetherianRing R] [IsCompleteLocalRing R]

-- Proof sketch: Propositions `15.50.12` and `15.48.7` give the `G`-ring and `J-2` conditions.
-- Remark `10.160.9` supplies universal catenarity via the Cohen structure theorem.
/-- Proposition 15.52.3 (2): Noetherian complete local rings are excellent. -/
instance isExcellentRing_of_noetherian_completeLocalRing : IsExcellentRing R := by
  letI : IsQuasiExcellentRing R := IsQuasiExcellentRing.mk
  let hUC : UniversallyCatenaryRing R := universallyCatenaryRing_of_isCompleteLocalRing R
  letI : UniversallyCatenaryRing R := hUC
  exact IsExcellentRing.mk hUC.catenary_of_finiteType

end

section

variable (R : Type u) [CommRing R] [IsDedekindDomain R] [CharZero (FractionRing R)]

/-- Helper for Proposition 15.52.3: the localization of a Dedekind domain at the zero prime is
regular local because it is the fraction field. -/
private theorem localizationAtPrime_isRegularLocalRing_of_zero_prime
    (p : PrimeSpectrum R) (hp : p.asIdeal = ⊥) :
    IsRegularLocalRing (Localization.AtPrime p.asIdeal) := by
  -- Replacing the prime by `0` turns the localization into the fraction field of `R`.
  subst hp
  letI : IsFractionRing R (Localization.AtPrime (⊥ : Ideal R)) := by
    delta IsFractionRing
    simpa [Ideal.primeCompl_bot] using
      (inferInstance :
        IsLocalization ((⊥ : Ideal R).primeCompl)
          (Localization.AtPrime (⊥ : Ideal R)))
  let _ : Field (Localization.AtPrime (⊥ : Ideal R)) :=
    IsFractionRing.toField (A := R) (K := Localization.AtPrime (⊥ : Ideal R))
  infer_instance

/-- Helper for Proposition 15.52.3: the localization of a Dedekind domain at a nonzero prime is
regular local because it is a discrete valuation ring. -/
private theorem localizationAtPrime_isRegularLocalRing_of_nonzero_prime
    (p : PrimeSpectrum R) (hp : p.asIdeal ≠ ⊥) :
    IsRegularLocalRing (Localization.AtPrime p.asIdeal) := by
  let Rp := Localization.AtPrime p.asIdeal
  -- A nonzero prime localization of a Dedekind domain is a DVR, hence regular local of dimension
  -- `1`.
  have hDvr : IsDiscreteValuationRing Rp := by
    simpa [Rp] using
      (IsLocalization.AtPrime.isDiscreteValuationRing_of_dedekind_domain R hp Rp)
  exact
    (discreteValuationRing_iff_regularLocalRing_dim_one (A := Rp)).mp
      ⟨inferInstance, hDvr⟩ |>.1

/-- Helper for Proposition 15.52.3: Dedekind domains are regular rings because each localization
at a prime is regular local. -/
private theorem dedekindDomain_isRegularRing : IsRegularRing R := by
  refine
    { toIsNoetherian := inferInstance
      isRegularLocalRing_atPrime := ?_ }
  intro p
  -- Split on whether the prime is `0`, matching the source proof's field/DVR dichotomy.
  by_cases hp : p.asIdeal = ⊥
  · exact localizationAtPrime_isRegularLocalRing_of_zero_prime (R := R) p hp
  · exact localizationAtPrime_isRegularLocalRing_of_nonzero_prime (R := R) p hp

-- Proof sketch: Propositions `15.50.12` and `15.48.7` give the `G`-ring and `J-2` conditions.
-- A Dedekind domain is regular, hence Cohen-Macaulay, so Lemma `10.105.9` gives universal
-- catenarity.
/-- Proposition 15.52.3 (4): Dedekind domains with fraction field of characteristic zero are
excellent. -/
instance dedekindDomain_isExcellentRing_of_fractionRing_charZero : IsExcellentRing R := by
  letI : IsQuasiExcellentRing R := IsQuasiExcellentRing.mk
  -- Route correction: follow the source proof through regularity and Cohen-Macaulayness, rather
  -- than searching for a separate Dedekind-specific catenarity theorem.
  letI : IsRegularRing R := dedekindDomain_isRegularRing (R := R)
  let hUC : UniversallyCatenaryRing R :=
    universallyCatenaryRing_of_cohenMacaulayRing inferInstance
  letI : UniversallyCatenaryRing R := hUC
  exact IsExcellentRing.mk hUC.catenary_of_finiteType

end

section

/- Proposition 15.52.3 (3): the ring of integers `ℤ` is excellent, by the
Dedekind-domain characteristic-zero instance above. -/
#check (inferInstance : IsExcellentRing ℤ)

end

section

variable {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S]

-- Proof sketch: finite type algebras over an excellent ring are `G`-rings by Proposition
-- `15.50.12`, `J-2` by Proposition `15.48.7`, and universally catenary by the essentially finite
-- type stability lemma. Combining these three facts yields excellence.
/-- Proposition 15.52.3 (5): finite type ring extensions of any of the preceding excellent rings
are excellent. -/
theorem isExcellentRing_of_finiteType [IsExcellentRing R] [Algebra.FiniteType R S] :
    IsExcellentRing S := by
  let hG : IsGRing S := isGRing_of_finiteType R
  letI : IsJ2Ring.{u, v} R := inferInstance
  let hJ2 : IsJ2Ring S := isJ2Ring_of_finiteType R
  let hQE : IsQuasiExcellentRing S := { toIsGRing := hG, toIsJ2Ring := hJ2 }
  letI : Algebra.EssFiniteType R S := inferInstance
  let hUC : UniversallyCatenaryRing S :=
    universallyCatenaryRing_of_essFiniteType R
  exact { toIsQuasiExcellentRing := hQE, catenary_of_finiteType := hUC.catenary_of_finiteType }

end
