import Mathlib
import Mathlib.Tactic.Recall
import StacksProject_2024.Chap13.Lemma_13_26_2
import StacksProject_2024.Chap13.Lemma_13_26_5

open CategoryTheory
open CategoryTheory.Limits
open scoped CategoryTheory

noncomputable section

universe u v

namespace CategoryTheory

/- Domain-style sampling for 13.26.13.3:
- primary domain: the filtered-injective full subcategory `𝓘^f ⊂ Fil^f(𝒜)` and the interval-split
  model for its objects;
- inspected owner declarations:
  `filteredInjectiveSubcategory`,
  `finiteFilteredObjectCat`,
  `Set.Icc`,
  `intervalSplitFilteredObject`,
  `isFilteredInjective_iff_exists_iso_intervalSplitFilteredObject`;
- owner abstraction: `filteredInjectiveSubcategory 𝒜`;
- primitive data: an object `I : filteredInjectiveSubcategory 𝒜`;
- derived API: an interval-split presentation of `I.obj` together with the tail-filtration
  formula inherited from `intervalSplitFilteredObject`.

Source/core/bridge triage:
- `source-facing`: the textbook consequence that a filtered injective object admits a tail
  biproduct model with the stated filtration formula;
- `core/canonical`: `filteredInjectiveSubcategory 𝒜`;
- `bridge/view`: `intervalSplitFilteredObject` from `Lemma_13_26_2`. -/

variable {𝒜 : Type u} [Category.{v} 𝒜] [Abelian 𝒜]

/- Lemma 13.26.2 already owns the interval-split decomposition of a filtered injective finite
filtered object. This file should reuse that owner theorem directly rather than restating it as a
parallel existential wrapper specialized to `𝓘^f(𝒜)`. -/
recall isFilteredInjective_iff_exists_iso_intervalSplitFilteredObject

section

variable (I : 𝓘^f(𝒜))

/- 13.26.13.3: if `I` is a filtered injective finite filtered object, then the forward direction
of the owner theorem gives an interval-indexed direct-sum presentation of `I.obj` by injective
summands. -/
#check
  (isFilteredInjective_iff_exists_iso_intervalSplitFilteredObject I.obj).1 inferInstance

end

/- In the interval-split model from Lemma 13.26.2, the filtration stage `F^p` is the canonical
tail subobject. This is the owner formula for `intervalSplitFilteredObject`, so it should also be
reused directly. -/
recall intervalSplitFilteredObject_filtration_obj

end CategoryTheory
