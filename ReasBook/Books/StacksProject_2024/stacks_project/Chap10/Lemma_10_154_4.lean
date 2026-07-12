import Mathlib
import StacksProject_2024.Chap10.Lemma_10_154_3

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory Limits
open CommRingCat
open CommRingCat.Hom

universe u v

namespace RingHom

section

variable {I : Type v} [Preorder I] [Nonempty I] [IsDirectedOrder I]

/- Domain-style sampling for Lemma 10.154.4:
* primary domain: filtered-colimit closure of ind-étale morphisms in the arrow category of
  commutative rings;
* sampled owner declarations:
  - `RingHom.IsFilteredColimitOfEtale`, the chapter source-facing owner for ind-étale ring maps;
  - `RingHom.filteredColimitOfEtale_baseChange`, the owner-level base-change theorem;
  - `RingHom.isFilteredColimitOfEtale_of_isColimit_filtered_system`, the fixed-source colimit
    theorem;
  - `CategoryTheory.MorphismProperty.ind`, the core filtered-colimit owner behind the wrapper.
* owner decision:
  - `source-facing`: `RingHom.isFilteredColimitOfEtale_colimit_of_directed_ringMap_system`;
  - `core/canonical`: `CategoryTheory.MorphismProperty.ind CommRingCat.etale`;
  - `bridge/view`: the wrapper `RingHom.IsFilteredColimitOfEtale`, which hides the same-universe
    `ULift` presentation of the core owner.
* primitive data: a directed diagram of ring maps in `Arrow CommRingCat` and the owner-level
  ind-étale hypothesis on each stage map;
* derived API: the induced owner-level ind-étale statement for the colimit map.

Since Lemma `10.154.3` already introduced `RingHom.IsFilteredColimitOfEtale` as the source-facing
owner, this file should use that owner directly instead of repeating the raw
`ind CommRingCat.etale` presentation in its public theorem surface.
-/

-- Proof sketch: view the directed system of ring maps as a diagram in `Arrow CommRingCat`. For
-- each stage, base change its étale presentation along the map from the source ring to the colimit
-- source using Lemma `10.154.1`. These base-changed presentations assemble into a filtered diagram
-- over the colimit source, and Lemma `10.154.3` upgrades the resulting filtered colimit
-- decomposition of the colimit target map to one by étale algebras.
/-- Lemma 10.154.4: if a directed system of commutative ring maps has the property that each stage
map is a filtered colimit of étale algebras over its source, then the colimit map from the
colimit of the source rings to the colimit of the target rings is also a filtered colimit of
étale algebras. -/
theorem isFilteredColimitOfEtale_colimit_of_directed_ringMap_system
    (F : I ⥤ Arrow CommRingCat.{u}) (c : Cocone F) (hc : IsColimit c)
    (hF : ∀ i, (hom (F.obj i).hom).IsFilteredColimitOfEtale) :
    (hom c.pt.hom).IsFilteredColimitOfEtale := sorry

end

end RingHom
