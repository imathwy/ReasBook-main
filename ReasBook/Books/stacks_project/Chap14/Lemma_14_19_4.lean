import Mathlib
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open CategoryTheory.SimplicialObject

noncomputable section

universe v u

namespace CategoryTheory

variable {C : Type u} [Category.{v} C]
variable {n : ℕ}
variable [∀ F : (SimplexCategory.Truncated n)ᵒᵖ ⥤ C,
  (SimplexCategory.Truncated.inclusion n).op.HasPointwiseRightKanExtension F]

/- Domain-style sampling for Lemma 14.19.4:
- primary domain: simplicial-object truncation/coskeleton adjunctions;
- sampled owner API:
  `truncation`,
  `Truncated.cosk`,
  `coskAdj`,
  `Functor.HasPointwiseRightKanExtension`;
- best owner abstraction: the source-facing comparison morphism is the counit component of the
  adjunction `truncation n ⊣ Truncated.cosk n`, and the numbered lemma is the derived statement
  that this counit is an isomorphism under the owner-level pointwise right-Kan-extension
  hypothesis;
- primitive data: the ambient category, the truncation level `n`, and the pointwise right Kan
  extensions along `(SimplexCategory.Truncated.inclusion n).op`;
- derived API: for every `n`-truncated simplicial object `U`, the canonical morphism
  `(coskAdj n).counit.app U :
    (truncation n).obj ((Truncated.cosk n).obj U) ⟶ U`
  is an isomorphism.

Source/core/bridge triage:
- `source-facing`: the canonical map `truncation n (coskₙ U) ⟶ U`;
- `core/canonical`: the counit natural transformation `(coskAdj n).counit`;
- `bridge/view`: downstream hypotheses such as finite limits or finite connected limits may be used
  elsewhere to produce the pointwise right-Kan-extension owner assumptions, but this file should
  state the canonical owner layer directly rather than importing one particular bridge.

This item adds no new mathematics beyond the owner API, so it should remain a direct canonical
recall of the counit-isomorphism instance rather than a local theorem shell. -/

recall coskAdj

variable (U : SimplicialObject.Truncated C n)

/- Lemma 14.19.4: for an `n`-truncated simplicial object `U`, whenever the pointwise right Kan
extensions defining `Truncated.cosk n` exist, the canonical morphism
`truncation n ((Truncated.cosk n).obj U) ⟶ U`, namely the counit component
`((coskAdj n).counit.app U)`, is an isomorphism. -/
#check (inferInstance : IsIso ((coskAdj n).counit.app U))

/- Mathlib also provides the stronger owner-level statement that the whole counit natural
transformation of `truncation n ⊣ Truncated.cosk n` is an isomorphism. -/
#check (inferInstance : IsIso (coskAdj n).counit)

end CategoryTheory
