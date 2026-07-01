import Mathlib
import stacks_project.Internal.Chap04.FibredInGroupoidsTwoFibreProductSquare
import stacks_project.Chap04.Definition_4_35_6
import stacks_project.Chap04.Lemma_4_33_10

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

namespace CategoryTheory

open CategoryOver

variable {C : Type u} [Category.{v} C]

/- Domain-style sampling for Lemma 4.35.7:
- primary domain: categories fibred in groupoids over a fixed base and their `2`-fibre products;
- inspected owner-level declarations:
  `IsFibredInGroupoids`,
  `FibredInGroupoidsOver`,
  `FibredInGroupoidsMor`,
  `FibredCategoryOver.twoFibreProduct`,
  `FibredCategoryOver.twoFibreProductSquare`,
  `FibredCategoryOver.twoFibreProduct_isTwoFibreProduct`,
  `FibredCategoryOver.twoFibreProductLeftProjection`,
  `FibredCategoryOver.twoFibreProductRightProjection`,
  `explicitTwoFibreProduct`;
- best owner abstraction: the source-facing statement for this item should live at the owner level
  `FibredInGroupoidsOver C`, with the canonical square and its `Bicategory.IsFinal` universal
  property obtained by restricting the ambient owner
  `FibredCategoryOver.twoFibreProductSquare`; the explicit pullback projection in `Cat/C` is the
  companion closure theorem feeding that owner-level statement.

Primitive-vs-derived split:
- primitive source-facing data: the based functors `F : X ⥤ᵇ S` and `G : Y ⥤ᵇ S` over `C`,
  with fibred-in-groupoids hypotheses on the source projections and fibredness of the target
  projection;
- derived API: the bundled owner-level rebundling
  `FibredInGroupoidsOver.twoFibreProduct`, its two projections, the canonical square
  `FibredInGroupoidsOver.twoFibreProductSquare`, and the resulting
  `FibredInGroupoidsOver.twoFibreProduct_isTwoFibreProduct`, all obtained by restricting the
  ambient owner `FibredCategoryOver.twoFibreProductSquare` to the full sub-`2`-category
  `FibredInGroupoidsOver C`.

Source/core/bridge triage:
- `source-facing`: `FibredInGroupoidsOver.twoFibreProductSquare` and
  `FibredInGroupoidsOver.twoFibreProduct_isTwoFibreProduct`;
- `core/canonical`: `IsFibredInGroupoids` on the explicit pullback projection in `Cat/C`;
- `bridge/view`: `explicitTwoFibreProductProjection_isFibredInGroupoids` and the owner-level
  rebundling `FibredInGroupoidsOver.twoFibreProduct`. -/

section Raw

variable {X Y S : BasedCategory C}

-- Proof sketch: apply Lemma `4.33.10` to the same explicit `2`-fibre-product model from
-- Lemma `4.32.3` using only that the target projection is fibred, then use Lemma `4.35.2` to
-- reduce the remaining work to checking that every fiber is a groupoid.
/-- Lemma 4.35.7 (1): if `F : X ⥤ᵇ S` and `G : Y ⥤ᵇ S` are based functors over `C` whose source
categories are fibred in groupoids and whose target category is fibred over `C`, then the
explicit `2`-fibre-product projection from Lemma 4.32.3 is again fibred in groupoids over `C`. -/
theorem explicitTwoFibreProductProjection_isFibredInGroupoids
    (F : X ⥤ᵇ S) (G : Y ⥤ᵇ S)
    [IsFibredInGroupoids X.p] [IsFibredInGroupoids Y.p] [S.p.IsFibered] :
    IsFibredInGroupoids (explicitTwoFibreProduct F G).p :=
  sorry

instance (F : X ⥤ᵇ S) (G : Y ⥤ᵇ S)
    [IsFibredInGroupoids X.p] [IsFibredInGroupoids Y.p] [S.p.IsFibered] :
    IsFibredInGroupoids (explicitTwoFibreProduct F G).p :=
  explicitTwoFibreProductProjection_isFibredInGroupoids F G

end Raw

namespace FibredInGroupoidsOver

variable {X Y S : FibredInGroupoidsOver C}

open FibredInGroupoidsMor

private theorem ambientTwoFibreProduct_isFibredInGroupoids
    (F : X ⟶ S) (G : Y ⟶ S) :
    IsFibredInGroupoids (FibredCategoryOver.twoFibreProduct F.toHom G.toHom).p := by
  change IsFibredInGroupoids
    (explicitTwoFibreProduct (toBasedFunctor F) (toBasedFunctor G)).p
  exact explicitTwoFibreProductProjection_isFibredInGroupoids (toBasedFunctor F) (toBasedFunctor G)

/-- The canonical fibred `2`-fibre product of morphisms of categories fibred in groupoids over
`C`, obtained by restricting the chapter-level owner `FibredCategoryOver.twoFibreProduct` to the
full sub-`2`-category `FibredInGroupoidsOver C`. -/
noncomputable abbrev twoFibreProduct
    (F : X ⟶ S) (G : Y ⟶ S) :
    FibredInGroupoidsOver C :=
  ⟨FibredCategoryOver.twoFibreProduct F.toHom G.toHom,
    ambientTwoFibreProduct_isFibredInGroupoids F G⟩

/-- The left projection from the canonical fibred `2`-fibre product of categories fibred in
groupoids over `C`. -/
noncomputable abbrev twoFibreProductLeftProjection
    (F : X ⟶ S) (G : Y ⟶ S) :
    twoFibreProduct F G ⟶ X :=
  ofAmbientHom (FibredCategoryOver.twoFibreProductLeftProjection F.toHom G.toHom)

/-- The right projection from the canonical fibred `2`-fibre product of categories fibred in
groupoids over `C`. -/
noncomputable abbrev twoFibreProductRightProjection
    (F : X ⟶ S) (G : Y ⟶ S) :
    twoFibreProduct F G ⟶ Y :=
  ofAmbientHom (FibredCategoryOver.twoFibreProductRightProjection F.toHom G.toHom)

/- The canonical `2`-commutative square in `FibredInGroupoidsOver C` for the two-fibre-product
construction above. -/
noncomputable def twoFibreProductSquare
    (F : X ⟶ S) (G : Y ⟶ S) :
    BicategoricalTwoCommutativeSquare F G :=
  mkTwoFibreProductSquare F G (ambientTwoFibreProduct_isFibredInGroupoids F G)

-- Proof sketch: use the ambient `FibredCategoryOver.twoFibreProductSquare` and restrict its
-- universal property along the full sub-`2`-category `FibredInGroupoidsOver C`.
/-- Lemma 4.35.7 (2): the canonical square `twoFibreProductSquare F G` is a bicategorical
`2`-fibre product in the `2`-category of categories fibred in groupoids over `C`. -/
theorem twoFibreProduct_isTwoFibreProduct
    (F : X ⟶ S) (G : Y ⟶ S) :
    Bicategory.IsFinal (twoFibreProductSquare F G) :=
  sorry

end FibredInGroupoidsOver

end CategoryTheory
