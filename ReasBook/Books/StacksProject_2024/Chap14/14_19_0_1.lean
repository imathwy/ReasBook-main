import Mathlib
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open CategoryTheory.SimplicialObject

noncomputable section

universe u v

namespace CategoryTheory

variable {C : Type u} [Category.{v} C]
variable {n : ℕ}
variable [∀ F : (SimplexCategory.Truncated n)ᵒᵖ ⥤ C,
  (SimplexCategory.Truncated.inclusion n).op.HasRightKanExtension F]

/- Domain-style sampling for 14.19.0.1:
- primary domain: simplicial-object truncation/coskeleton adjunctions;
- sampled owner API:
  `truncation`,
  `Truncated.cosk`,
  `coskAdj`,
  `Adjunction.homEquiv`;
- source/core/bridge triage:
  `source-facing`: the Hom-set bijection `Mor(U, coskₙ V) ≃ Mor(skₙ U, V)`;
  `core/canonical`: the adjunction owner `(coskAdj n).homEquiv`;
  `bridge/view`: the source's orientation is the symmetric form of that canonical equivalence.

Primitive data are only the simplicial object `U`, the `n`-truncated simplicial object `V`, and
the existence of the right Kan extensions defining `Truncated.cosk n`. The Hom-set bijection is
derived API of the adjunction owner, so this item should recall/use that owner directly rather
than introduce a parallel local `abbrev`. -/

section

variable (U : SimplicialObject C) (V : SimplicialObject.Truncated C n)

/- 14.19.0.1: morphisms from a simplicial object `U` to the `n`-coskeleton of an
`n`-truncated simplicial object `V` are naturally equivalent to morphisms from the `n`-truncation
of `U` to `V`. This is exactly the symmetric form of the canonical Hom-set equivalence of the
adjunction `truncation n ⊣ Truncated.cosk n`. -/
recall coskAdj

#check ((coskAdj n).homEquiv U V).symm

end

end CategoryTheory
