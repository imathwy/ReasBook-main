import Mathlib
import StacksProject_2024.stacks_project.Chap10.Lemma_10_154_3

-- Declarations for this item will be appended below by the statement pipeline.

universe u v w

namespace RingHom

section

variable {R : Type u} {A : Type v} {B : Type w} [CommRing R] [CommRing A] [CommRing B]
variable [Algebra R A] [Algebra R B] [Algebra A B] [IsScalarTower R A B]

/- Domain-style sampling for Lemma 10.154.5:
* primary domain: filtered-colimit closure of étale ring maps in commutative algebra, specialized
  to a common-base comparison map `A → B`;
* sampled owner declarations:
  - `RingHom.IsFilteredColimitOfEtale`, the chapter source-facing owner for ind-étale ring maps;
  - `RingHom.filteredColimitOfEtale_baseChange`, the owner-level base-change theorem;
  - `RingHom.isFilteredColimitOfEtale_comp`, the owner-level composition theorem;
  - `Algebra.etale_of_etale_over_common_base`, the stagewise common-base étale owner.
* owner decision:
  - `source-facing`: the Stacks lemma for the structural map `A → B` under common-base
    ind-étale hypotheses over `R`;
  - `core/canonical`: `CategoryTheory.MorphismProperty.ind CommRingCat.etale`;
  - `bridge/view`: the wrapper `RingHom.IsFilteredColimitOfEtale`, which hides the `ULift`
    presentation of the categorical owner across possibly different universes.
* primitive data: only the owner-level ind-étale hypotheses on `R → A` and `R → B`, together with
  the given `A`-algebra structure on `B`;
* derived API: the induced owner-level ind-étale statement for `A → B`.

This file should therefore speak directly through `RingHom.IsFilteredColimitOfEtale` rather than
repeating the raw `ind CommRingCat.etale (ofHom ...)` presentation or reintroducing an unnecessary
same-universe restriction in its public theorem surface.
-/

-- Proof sketch: write `A` and `B` as filtered colimits of étale `R`-algebras. For each étale
-- stage `Aᵢ → A`, finite presentation factors the composite `Aᵢ → B` through some étale
-- `R`-stage `Bⱼ → B`. By Lemma `10.143.8`, the induced map `Aᵢ → Bⱼ` is étale, and then base
-- change along `Aᵢ → A` keeps it étale over `A`. These tensor-product stages form a filtered
-- system whose colimit is `B`, yielding the desired presentation over `A`.
/-- Lemma 10.154.5: if `A` and `B` are filtered colimits of étale `R`-algebras and `B` is an
`A`-algebra over `R`, then `A → B` is a filtered colimit of étale `A`-algebras. -/
theorem isFilteredColimitOfEtale_of_isFilteredColimitOfEtale_over_common_base
    (hA : (algebraMap R A).IsFilteredColimitOfEtale)
    (hB : (algebraMap R B).IsFilteredColimitOfEtale) :
    (algebraMap A B).IsFilteredColimitOfEtale := sorry

end

end RingHom
