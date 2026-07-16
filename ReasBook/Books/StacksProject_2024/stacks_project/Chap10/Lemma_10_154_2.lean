import Mathlib
import StacksProject_2024.stacks_project.Chap10.Lemma_10_154_3

-- Declarations for this item will be appended below by the statement pipeline.

universe u v w

namespace RingHom

section

/- Domain-style sampling:
* primary domain: composition closure for ind-étale morphisms in commutative algebra;
* owner declarations inspected:
  - `CategoryTheory.MorphismProperty.ind`;
  - `CategoryTheory.MorphismProperty.IsStableUnderComposition.ind_of_preIndSpreads`;
  - `CommRingCat.etale`;
  - `RingHom.IsFilteredColimitOfEtale`.
* owner decision:
  - `source-facing`: `RingHom.isFilteredColimitOfEtale_comp`;
  - `core/canonical`: `CategoryTheory.MorphismProperty.ind CommRingCat.etale`;
  - `bridge/view`: the `ULift`-based same-universe presentation hidden inside
    `RingHom.IsFilteredColimitOfEtale`.

Primitive data are just the composable ring maps `f`, `g` and their owner-level ind-étale
hypotheses. The universe-lift bookkeeping is derived bridge data and should stay hidden in the
source-facing owner rather than reappearing as a same-universe restriction on `A`, `B`, and `C`.
-/

variable {A : Type u} {B : Type v} {C : Type w} [CommRing A] [CommRing B] [CommRing C]

-- Proof sketch: present `B` as a filtered colimit of étale `A`-algebras and `C` as a filtered
-- colimit of étale `B`-algebras. For a finitely presented `A`-algebra mapping to `C`, first factor
-- through some étale `B`-stage by finite presentation, then descend that stage to an étale
-- `A`-algebra by the base-change descent result of Lemma `10.143.3`. The factorization criterion
-- from Lemma `10.127.4` then shows that `A → C` is a filtered colimit of étale maps.
/-- Lemma 10.154.2: the composite of two ring maps that are filtered colimits of étale ring maps
is again a filtered colimit of étale ring maps. -/
theorem isFilteredColimitOfEtale_comp
    (f : A →+* B) (g : B →+* C)
    (hf : f.IsFilteredColimitOfEtale)
    (hg : g.IsFilteredColimitOfEtale) :
    (g.comp f).IsFilteredColimitOfEtale := sorry

end

end RingHom
