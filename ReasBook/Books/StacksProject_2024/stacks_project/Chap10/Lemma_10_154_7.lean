import Mathlib
import StacksProject_2024.stacks_project.Chap10.Lemma_10_154_3

-- Declarations for this item will be appended below by the statement pipeline.

open IsLocalRing
open RingHom

universe u

section

variable {R S S' K : Type u}
variable [CommRing R] [CommRing S] [CommRing S'] [Field K]
variable [Algebra R S] [Algebra R S'] [Algebra R K]
variable [Algebra S K] [Algebra S' K]
variable [IsScalarTower R S K] [IsScalarTower R S' K]
variable [HenselianLocalRing S] [HenselianLocalRing S']
variable [IsLocalHom (algebraMap S K)] [IsLocalHom (algebraMap S' K)]

/- Domain-style sampling:
- primary domain: henselian local rings, filtered colimits of étale algebras, and residue-field
  comparisons through maps to a common field;
- sampled owner declarations of the same kind:
  `HenselianLocalRing`,
  `RingHom.IsFilteredColimitOfEtale`,
  `existsUnique_algHom_of_filteredColimitOfEtale_of_henselianLocal_of_residueFieldMap`,
  `ResidueField.lift`;
- best owner abstraction: the canonical owners here are `HenselianLocalRing`,
  `IsLocalHom`, and `RingHom.IsFilteredColimitOfEtale`; the present lemma stays
  `source-facing`, since it adds the extra mathematical content of comparing two henselian local
  `R`-algebras through a common residue field target `K`;
- primitive data vs. derived API:
  the primitive inputs are the two ind-étale `R`-algebra structures and the two bijective
  residue-field comparison maps to `K`;
  the derived API is the unique compatible `R`-algebra equivalence `S ≃ₐ[R] S'`.

Source/core/bridge triage:
- `source-facing`: the present uniqueness statement for two henselian local `R`-algebras with a
  common residue-field identification;
- `core/canonical`: `HenselianLocalRing`, `IsLocalHom`, `RingHom.IsFilteredColimitOfEtale`, and
  `existsUnique_algHom_of_filteredColimitOfEtale_of_henselianLocal_of_residueFieldMap`;
- `bridge/view`: the chosen field `K` and the bijectivity of `ResidueField.lift` for the two
  structural maps.
-/

-- Proof sketch: apply Lemma `10.154.6` with `A = S` and target `S'`, using the map
-- `ResidueField.lift (algebraMap S K)` composed with the inverse of
-- `ResidueField.lift (algebraMap S' K)` to obtain a unique `R`-algebra map `S → S'`
-- compatible with the maps to `K`, and similarly a unique map `S' → S`. The two composites are
-- the unique endomorphisms compatible with the corresponding maps to `K`, so they are identities;
-- hence the two maps are inverse `R`-algebra isomorphisms, unique by the same compatibility
-- condition.
/-- Lemma 10.154.7: given a commutative diagram `S → K ← S'` over `R` in which `S` and `S'` are
henselian local rings, both are filtered colimits of étale `R`-algebras, and the maps to the
field `K` identify `K` with the residue field of each source, there exists a unique
`R`-algebra isomorphism `S ≃ₐ[R] S'` compatible with the maps to `K`. -/
lemma existsUnique_algEquiv_of_henselianLocal_of_filteredColimitOfEtale_of_common_residueField
    (hS : (algebraMap R S).IsFilteredColimitOfEtale)
    (hS' : (algebraMap R S').IsFilteredColimitOfEtale)
    (hκ : Function.Bijective (ResidueField.lift (algebraMap S K)))
    (hκ' : Function.Bijective (ResidueField.lift (algebraMap S' K))) :
    ∃! e : S ≃ₐ[R] S', (algebraMap S' K).comp (e : S →+* S') = algebraMap S K := sorry

end
