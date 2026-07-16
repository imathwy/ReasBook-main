import Mathlib
import Mathlib.RingTheory.Henselian
import StacksProject_2024.stacks_project.Chap10.Lemma_10_154_3

-- Declarations for this item will be appended below by the statement pipeline.

open IsLocalRing

universe u

section

variable (R : Type u) [CommRing R] [IsLocalRing R]
variable (S : Type u) [CommRing S] [Algebra R S]

/-
Domain-style sampling:
- primary domain: henselian local rings and henselization maps of local rings;
- sampled owner declarations of the same kind:
  `HenselianLocalRing`,
  `IsLocalHom`,
  `RingHom.IsFilteredColimitOfEtale`,
  `RingHom.algebraMap_isFilteredColimitOfEtale_of_isColimit`;
- best owner abstraction: there is no upstream bundled henselization owner in mathlib, so the
  source-facing owner here should be the class `IsHenselizationOf R S`, assembled from the
  canonical owners for henselianity, locality, and filtered-colimit-of-étale presentation;
- primitive data: the henselian local target, the local structural map, the filtered-colimit-of-
  étale presentation, the maximal-ideal image equality, and bijectivity on residue fields;
- derived API: the canonical residue-field equivalence induced by the structural map.

Source/core/bridge triage:
- `source-facing`: `IsHenselizationOf` and `exists_henselization`;
- `core/canonical`: `HenselianLocalRing`, `IsLocalHom`, and `RingHom.IsFilteredColimitOfEtale`;
- `bridge/view`: `IsHenselizationOf.residueFieldEquiv`.
-/
/-- An `R`-algebra `S` is a henselization of the local ring `R` if `R → S` is a local map, `S` is
henselian, `S` is a filtered colimit of étale `R`-algebras, the maximal ideal of `S` is the image
of the maximal ideal of `R`, and the induced residue-field map is bijective. -/
class IsHenselizationOf : Prop extends HenselianLocalRing S, IsLocalHom (algebraMap R S) where
  isFilteredColimitOfEtale :
    (algebraMap R S).IsFilteredColimitOfEtale
  map_maximalIdeal :
    Ideal.map (algebraMap R S) (maximalIdeal R) = maximalIdeal S
  residueField_bijective :
    Function.Bijective (ResidueField.map (algebraMap R S))

namespace IsHenselizationOf

variable {R : Type u} [CommRing R] [IsLocalRing R]
variable {S : Type u} [CommRing S] [Algebra R S] [IsHenselizationOf R S]

/-- The canonical residue-field isomorphism induced by a henselization. -/
noncomputable def residueFieldEquiv : ResidueField R ≃+* ResidueField S :=
  RingEquiv.ofBijective (ResidueField.map (algebraMap R S))
    IsHenselizationOf.residueField_bijective

end IsHenselizationOf

-- Proof sketch: define `Rʰ` as the filtered colimit of étale local `R`-algebras whose residue
-- field over `ResidueField R` is unchanged. The filtered-colimit-of-étale property is built into
-- the construction, the local and maximal-ideal statements come from the unique prime over the
-- closed point, the residue-field map is the canonical colimit identification, and henselianity
-- follows by descending a monic polynomial with a simple residue-field root to some étale stage
-- and lifting that root there.
/-- Lemma 10.155.1: every local ring admits a henselization `R → Rʰ`, namely a local map to a
henselian local ring that is a filtered colimit of étale `R`-algebras, whose maximal ideal is the
image of `maximalIdeal R`, and whose residue field agrees with `ResidueField R`. -/
theorem exists_henselization :
    ∃ (Rh : Type u) (_ : CommRing Rh) (_ : Algebra R Rh), IsHenselizationOf R Rh := sorry

end
