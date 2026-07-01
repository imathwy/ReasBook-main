import Mathlib
import Mathlib.Tactic.Recall
import stacks_project.Chap04.Lemma_4_33_10
import stacks_project.Chap04.Lemma_4_35_7
import stacks_project.Chap08.Definition_8_4_1

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open FibredCategoryOver

universe u v vDesc

namespace CategoryTheory

/- Domain-style sampling for Lemma 8.4.6:
- primary domain: stacks over a site and bicategorical `2`-fibre products of fibred categories.
- inspected owner-level declarations:
  `FibredCategoryOver.twoFibreProduct`,
  `FibredInGroupoidsOver.twoFibreProduct`,
  `IsStackOnSite`,
  `isStackOnSite_of_isStack`.
- best owner abstraction: the source-facing stack conclusion should stay on the canonical fibred
  `2`-fibre product `FibredCategoryOver.twoFibreProduct F G`, while the inherited
  fibred-in-groupoids structure should be reused through the Chapter-4 owner
  `FibredInGroupoidsOver.twoFibreProduct`; any later rebundling into stacks is a downstream bridge
  and not part of this file's owner-level API.
- primitive data: the canonical fibred `2`-fibre product from Chapter 4, its owner-level
  rebundling in `FibredInGroupoidsOver`, and the canonical fibers of the resulting projection.
- derived API: the stack theorem for the projection and the resulting instance on
  `(FibredCategoryOver.twoFibreProduct F G).p`.

Source/core/bridge triage:
- `source-facing`: `stackTwoFibreProduct_isStack`.
- `core/canonical`: `FibredCategoryOver.twoFibreProduct F G`,
  `FibredInGroupoidsOver.twoFibreProduct`, and `IsStackOnSite`.
- `bridge/view`: no additional bridge owner is introduced here; downstream files may repackage
  the result as needed. -/

attribute [instance] FibredCategoryOver.isFibred

section

variable {C : Type u} [Category.{v} C]
variable {J : GrothendieckTopology C}
variable {X Y S : FibredCategoryOver C}
variable (F : FibredCategoryMor X S) (G : FibredCategoryMor Y S)

instance
    [IsFibredInGroupoids X.p] [IsFibredInGroupoids Y.p] [IsFibredInGroupoids S.p] :
    IsFibredInGroupoids (twoFibreProduct F G).p := by
  change IsFibredInGroupoids
    (CategoryOver.explicitTwoFibreProduct
      F.toHom
      G.toHom).p
  exact explicitTwoFibreProductProjection_isFibredInGroupoids
    F.toHom
    G.toHom

/-- The explicit `2`-fibre-product projection carries the canonical fiber categories given by its
standard fibers. -/
private noncomputable instance :
    HasFibers (twoFibreProduct F G).p :=
  HasFibers.canonical (twoFibreProduct F G).p

/- Companion recall: Categories Lemma 4.32.3 is formalized by the canonical strict
`2`-fibre-product theorem on the explicit square. -/
recall CategoryOver.explicitTwoFibreProduct_isTwoFibreProduct

-- Proof sketch: the morphism presheaves in the explicit model are pullbacks of morphism
-- presheaves in `X`, `Y`, and `S`, hence are sheaves. For effective descent, descend the
-- `X`- and `Y`-components separately, then glue the comparison isomorphisms in `S` by the sheaf
-- property of the corresponding isomorphism presheaf.
/-- Lemma 8.4.6: the `(2,1)`-category of stacks over the site `(C, J)` has `2`-fibre products,
described by Categories, Lemma 4.32.3. Equivalently, for morphisms of stacks
`F : X ⟶ S` and `G : Y ⟶ S`, the bundled fibred `2`-fibre product from Categories,
Lemma 4.33.10 is again a stack over `(C, J)`. -/
theorem stackTwoFibreProduct_isStack
    [IsStackOnSite J X.p] [IsStackOnSite J Y.p] [IsStackOnSite J S.p] :
    IsStackOnSite J (twoFibreProduct F G).p := sorry

instance
    [IsStackOnSite J X.p] [IsStackOnSite J Y.p] [IsStackOnSite J S.p] :
    IsStackOnSite J (twoFibreProduct F G).p :=
  stackTwoFibreProduct_isStack F G

end

end CategoryTheory
