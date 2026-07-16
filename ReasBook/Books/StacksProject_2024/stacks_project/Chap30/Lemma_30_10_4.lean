import Mathlib
import StacksProject_2024.stacks_project.Chap17.Definition_17_12_1
import StacksProject_2024.stacks_project.Chap18.Definition_18_23_1

-- Declarations for this item will be appended below by the statement pipeline.

open AlgebraicGeometry
open CategoryTheory

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Modules

variable {X : Scheme.{u}} [IsNoetherian X]

-- Semantic recall: `lean_leansearch` surfaced the Grothendieck-abelian subobject colimit owner
-- `CategoryTheory.IsGrothendieckAbelian.isColimitMapCoconeOfSubobjectMkEqISup`, while local
-- project precedent records filtered-colimit presentations by a canonical subtype family together
-- with `Directed` and least-upper-bound/top-generation theorems. For this Stacks item, the
-- source-facing family is the subtype of coherent subobjects of the given quasi-coherent module.

/-- Lemma 30.10.4 (1): for a quasi-coherent `\mathcal O_X`-module `ℱ` on a Noetherian scheme
`X`, the family of coherent submodules of `ℱ` is directed by inclusion. -/
@[stacks 0GN6]
theorem directed_coherentSubobjects
    (ℱ : X.Modules) [ℱ.IsQuasicoherent] :
    Directed (· ≤ ·)
      (Subtype.val :
        { K : Subobject ℱ // ((K : X.Modules)).IsCoherent } → Subobject ℱ) := sorry

/-- Lemma 30.10.4 (2): for a quasi-coherent `\mathcal O_X`-module `ℱ` on a Noetherian scheme
`X`, the coherent submodules have `⊤` as their least upper bound. Equivalently, `ℱ` is the
filtered colimit of its coherent submodules. -/
@[stacks 0GN6]
theorem coherentSubobjects_isLUB_top
    (ℱ : X.Modules) [ℱ.IsQuasicoherent] :
    IsLUB
      (Set.range
        (Subtype.val :
          { K : Subobject ℱ // ((K : X.Modules)).IsCoherent } → Subobject ℱ))
      (⊤ : Subobject ℱ) := sorry

end AlgebraicGeometry.Scheme.Modules
