import Mathlib
import Mathlib.Tactic.Recall
import StacksProject_2024.stacks_project.Chap25.Definition_25_2_1

-- Declarations for this item will be appended below by the statement pipeline.

universe w v u

namespace CategoryTheory

open CategoryTheory.Limits
open scoped CategoryTheory.SemiRepresentableFamily

namespace Limits.FormalCoproduct.Hom

/- Domain-style sampling for Remark 25.12.7:
- primary domain: morphisms of semi-representable families and the induced morphisms between the
  coproducts of their component families;
- sampled owner declarations:
  `CategoryTheory.Limits.Sigma.map'`,
  `CategoryTheory.Limits.Sigma.ι_comp_map'`,
  `CategoryTheory.Limits.Sigma.map'_id_id`,
  `CategoryTheory.Limits.Sigma.map'_comp_map'`;
- best owner abstraction: the canonical coproduct map attached to a family-index map and
  component morphisms is already `Sigma.map'`;
- primitive data: a morphism `φ : K ⟶ L` in the canonical owner `FormalCoproduct`, equivalently a
  function on indices together with the component maps;
- derived API: the coproduct-inclusion formula and the identity/composition functoriality lemmas
  for `Sigma.map'`.

Source/core/bridge triage:
- `source-facing`: the induced map between the coproducts attached to a morphism of
  semi-representable families;
- `core/canonical`: `Sigma.map'` and its canonical compatibility lemmas;
- `bridge/view`: specializing those canonical declarations to morphisms in
  `CategoryTheory.Limits.FormalCoproduct`.

This item adds no new owner beyond the existing `Sigma.map'` API, so the refined file keeps a
direct recall/check surface rather than an exact-interface wrapper `coproductMap`. -/

variable {C : Type u} [Category.{v} C]
variable {K L : SR(C)}
variable [HasCoproduct K.obj] [HasCoproduct L.obj]

/- Remark 25.12.7: if the coproducts of the component families of `K` and `L` exist, then a
morphism `φ : K ⟶ L` induces a morphism from the coproduct of the components of `K` to the
coproduct of the components of `L`. In the canonical owner API this induced map is
`Sigma.map' φ.f φ.φ`. -/
#check (fun φ : K ⟶ L ↦ Sigma.map' φ.f φ.φ : (K ⟶ L) → ((∐ K.obj) ⟶ ∐ L.obj))

/- Companion recall: precomposing the induced coproduct map with the `i`th coproduct inclusion
recovers the component morphism landing in the `φ.f i`th target summand. -/
recall Sigma.ι_comp_map'

/- Companion recall: the induced coproduct map for the identity morphism is the identity. -/
recall Sigma.map'_id_id

/- Companion recall: passing to coproducts sends composition of family morphisms to composition of
the induced coproduct maps. -/
recall Sigma.map'_comp_map'

end Limits.FormalCoproduct.Hom

end CategoryTheory
