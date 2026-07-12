import Mathlib
import Mathlib.CategoryTheory.Limits.Shapes.BinaryProducts
import Mathlib.Tactic.Recall
import StacksProject_2024.Chap18.Lemma_18_19_2

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open SheafOfModules.RingedSite

noncomputable section

namespace SheafOfModules.RingedSite

/- Domain-style sampling for Lemma 18.27.9:
- primary domain: tensor comparison for localized restriction and extension by zero on a ringed
  site;
- sampled owner declarations:
  `ringedSiteLocalizedRestriction`,
  `ringedSiteLocalizedExtensionByZero`,
  `CategoryTheory.Adjunction.rightAdjointLaxMonoidal`,
  `CategoryTheory.Adjunction.leftAdjointOplaxMonoidal`;
- best owner abstraction:
  the Chapter 18 localized restriction / extension-by-zero owners together with the generic
  monoidal-adjunction API for their tensor comparison data;
- primitive data:
  the localized adjunction from `Lemma_18_19_2`;
- derived API:
  the lax/oplax monoidal comparison morphisms carried by that adjunction.

Source/core/bridge triage:
- `source-facing`: the tensor comparison for localization and extension by zero;
- `core/canonical`: the generic monoidal-adjunction owners
  `Adjunction.rightAdjointLaxMonoidal` and `Adjunction.leftAdjointOplaxMonoidal`;
- `bridge/view`: the specialization to
  `ringedSiteLocalizedRestriction J 𝒪 U` and `ringedSiteLocalizedExtensionByZero J 𝒪 U`.

This file therefore stays at the `bridge/view` layer and recalls the actual owners rather than
keeping the previous broken local theorem shell, whose statement mixed the localized pushforward
owner with the lower-shriek adjunction data in a non-type-correct way. -/

/- Lemma 18.27.9: the localized restriction and extension-by-zero functors are the Chapter 18
owners on which the tensor-comparison data lives. -/
recall ringedSiteLocalizedRestriction
recall ringedSiteLocalizedExtensionByZero

/- The monoidal comparison data itself is owned by the generic monoidal-adjunction API. -/
recall CategoryTheory.Adjunction.rightAdjointLaxMonoidal
recall CategoryTheory.Adjunction.leftAdjointOplaxMonoidal

end SheafOfModules.RingedSite
