import Mathlib
import stacks_project.Chap15.Lemma_15_12_7

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open RingPairCat

universe u v

noncomputable section

section

variable {A : Type u} [CommRing A]
variable {ι : Type v}
variable [RingPairCat.henselianPairInclusion.IsRightAdjoint]

/-
Domain-style sampling:
- primary domain: pair henselization in Chapter 15, with owner surface
  `henselizationRing (pairOfIdeal I)` and functoriality via `henselizationRingMap`;
- sampled same-kind declarations:
  `henselizationRing`,
  `toHenselization`,
  `henselizationRingMap`,
  `henselizationRing_existsUnique_algEquiv_of_zeroLocus_eq`;
- best owner abstraction: the canonical chosen henselization owner from `Lemma_15_12_1`, not a
  fresh public parameter for an arbitrary left adjoint to `henselianPairInclusion`;
- primitive data: `henselizationRing (pairOfIdeal I)`;
- derived API: the comparison map from the henselization of an intersection to the product of the
  henselizations of the components, and its bijectivity under pairwise comaximality.

Source/core/bridge triage:
- `source-facing`: `henselizationIntersectionToPi` and its bijectivity theorem;
- `core/canonical`: `henselizationRing`, `pairOfIdeal`, `toHenselization`, and
  `henselizationRingMap`;
- `bridge/view`: the product comparison map assembled from the canonical maps
  `henselizationRingMap (pairOfIdealMap (⨅ j, I j) (I i) (iInf_le I i))`.
-/

/-- The natural comparison map from the henselization ring of the intersection pair to the
product of the henselization rings of the component pairs. -/
def henselizationIntersectionToPi (I : ι → Ideal A) :
    henselizationRing (pairOfIdeal (⨅ j, I j)) →+*
      ∀ i : ι, henselizationRing (pairOfIdeal (I i)) :=
  Pi.ringHom fun i ↦
    henselizationRingMap (pairOfIdealMap (⨅ j, I j) (I i) (iInf_le I i))

-- Proof sketch: argue by induction on the finite index set, reducing to the case of two ideals by
-- grouping all but one ideal into their intersection. For two pairwise comaximal ideals, the
-- Chinese remainder theorem identifies the special fibres, and the universal property of pair
-- henselization upgrades that decomposition to an isomorphism of henselizations.
/-- Lemma 15.12.8: for a finite nonempty family of pairwise comaximal ideals in `A`, the chosen
henselization of the intersection pair `(A, ⋂ i, I i)` has a natural comparison map to the
product of the henselizations of `(A, I i)`, and that map is bijective. -/
theorem henselizationIntersectionToPi_bijective [Finite ι] [Nonempty ι]
    (I : ι → Ideal A) (hI : Pairwise fun i j ↦ IsCoprime (I i) (I j)) :
    Function.Bijective (henselizationIntersectionToPi I) := sorry

end
