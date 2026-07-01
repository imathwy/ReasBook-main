import Mathlib
import stacks_project.Chap10.Lemma_10_159_3
import stacks_project.Chap15.Lemma_15_50_2
import stacks_project.Chap15.Proposition_15_50_12

-- Declarations for this item will be appended below by the statement pipeline.

open Algebra

universe u

section

variable {R : Type u} [CommRing R] [IsNoetherianRing R]

/- Domain triage:
- primary domain: `G`-rings and regularity of formal fibres under finite free base change;
- sampled owner declarations:
  `Ideal.Fiber`,
  `IsGRing`,
  `isGRing_iff_forall_primePair_formalFiber_isGeometricallyRegular`,
  `isGRing_of_finiteType`,
  `exists_finiteFree_with_prime_extendedIdeal_and_residueField_equiv`;
- best owner abstraction: the chapter owner `IsGRing`, with the source-facing finite-free
  regular-formal-fibre criterion as the theorem surface and the canonical fiber owner
  `Ideal.Fiber`; Lemma `15.50.2` is only the bridge to geometric regularity;
- primitive data: the Noetherian ring `R` and a finite free `R`-algebra `S`;
- derived API: the owner-level companion criterion `IsGRing S`.

Layering:
- the numbered lemma is `source-facing`;
- `IsGRing` is the `core/canonical` owner;
- the prime-pair geometric-regularity criterion is the `bridge/view`.
-/
-- Proof sketch: for the forward implication, finite free algebras are finite type, so the
-- source-facing finite-type transfer theorem `isGRing_of_finiteType` makes every such algebra a
-- `G`-ring; Lemma
-- `15.50.2` then upgrades each formal fibre to geometric regularity, hence to ordinary
-- regularity. Conversely, to prove that `R` is a `G`-ring it is enough by Lemma `15.50.2` to show
-- geometric regularity of each formal fibre of `R`. By Definition `10.166.2`, that geometric
-- regularity is tested after finite purely inseparable residue-field extensions, and
-- `exists_finiteFree_with_prime_extendedIdeal_and_residueField_equiv` realizes those extensions by
-- finite free algebras. The resulting formal fibres of the finite free algebra localize the
-- corresponding tensor base changes of the original formal fibre, so the assumed regularity of all
-- finite-free formal fibres forces the needed geometric regularity.
/-- Lemma 15.50.4: for a Noetherian commutative ring `R`, `R` is a `G`-ring if and only if every
finite free `R`-algebra has regular formal fibre rings. -/
theorem isGRing_iff_forall_finiteFree :
    IsGRing R ↔
      ∀ (S : Type u) [CommRing S] [Algebra R S] [Module.Free R S] [Module.Finite R S]
        (p q : PrimeSpectrum S) (hqp : q.asIdeal ≤ p.asIdeal),
          IsRegularRing (q.asIdeal.Fiber (R̂_[p])) := by
  refine ⟨?_, ?_⟩
  · intro hR S _ _ _ _ p q hqp
    letI : IsGRing R := hR
    letI : Algebra.FiniteType R S := Module.Finite.finiteType S
    have hS : IsGRing S := by
      exact isGRing_of_finiteType R
    letI : IsGRing S := hS
    letI : IsGeometricallyRegular q.asIdeal.ResidueField (q.asIdeal.Fiber (R̂_[p])) :=
      (isGRing_iff_forall_primePair_formalFiber_isGeometricallyRegular S).1 hS p q hqp
    exact isRegularRing_of_isGeometricallyRegular q.asIdeal.ResidueField
      (q.asIdeal.Fiber (R̂_[p]))
  · intro hfiniteFree
    refine (isGRing_iff_forall_primePair_formalFiber_isGeometricallyRegular R).2 ?_
    intro p q hqp
    rw [isGeometricallyRegular_iff_forall_finite_purelyInseparable_tensorBaseChange_isRegularRing]
    intro K _ _ _ _
    obtain ⟨S, _, _, _, _, hqSPrime, hqSLiesOver, hResidue⟩ := by
      simpa using
        (exists_finiteFree_with_prime_extendedIdeal_and_residueField_equiv q.asIdeal K)
    letI : (q.asIdeal.map (algebraMap R S)).IsPrime := hqSPrime
    letI : (q.asIdeal.map (algebraMap R S)).LiesOver q.asIdeal := hqSLiesOver
    rcases hResidue with ⟨eK⟩
    let _ :
        (q.asIdeal.map (algebraMap R S)).ResidueField ≃ₐ[q.asIdeal.ResidueField] K := eK
    sorry

end
