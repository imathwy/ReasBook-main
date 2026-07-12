import Mathlib
import StacksProject_2024.Internal.Chap04.FibredInSetoidsTwoFibreProduct

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

namespace CategoryTheory

variable {C : Type u} [Category.{v} C]
variable {X Y S : FibredInSetoidsOver C}

/- Domain-style sampling for Lemma 4.39.4:
- primary domain: categories fibred in setoids over a fixed base and their bicategorical
  `2`-fibre products;
- inspected owner-level declarations:
  `IsFibredInSetoids`,
  `FibredInSetoidsOver`,
  `FibredInSetoidsOver.twoFibreProduct`,
  `FibredInGroupoidsOver.twoFibreProductSquare`;
- best owner abstraction: the primitive owner data already lives upstream in the canonical rebundled
  pullback object `FibredInSetoidsOver.twoFibreProduct`, so this file should keep only the
  source-facing bicategorical square and its universal property.

Primitive-vs-derived split:
- primitive source-facing data: the morphisms `F : X ⟶ S` and `G : Y ⟶ S`, together with the
  canonical owner `FibredInSetoidsOver.twoFibreProduct F G`;
- derived API: the inherited bicategorical square and the finality statement obtained by
  restricting the ambient fibred-in-groupoids pullback square.

Source/core/bridge triage:
- `source-facing`: `FibredInSetoidsOver.twoFibreProductSquare` and
  `FibredInSetoidsOver.twoFibreProduct_isTwoFibreProduct`;
- `core/canonical`: `FibredInSetoidsOver.twoFibreProduct` and
  `FibredInGroupoidsOver.twoFibreProductSquare`;
- `bridge/view`: the ambient projection morphisms and comparison `2`-isomorphism, read in
  `FibredInSetoidsOver C` through `ofAmbientHom` and `ofAmbientIso`. -/

namespace FibredInSetoidsOver

/-- The ambient fibred-in-groupoids pullback underlying `twoFibreProduct F G` also satisfies the
fibred-in-setoids condition. -/
private theorem ambientTwoFibreProduct_isFibredInSetoids
    (F : X ⟶ S) (G : Y ⟶ S) :
    IsFibredInSetoids (FibredInGroupoidsOver.twoFibreProduct F.toHom G.toHom).p := by
  let T : FibredInSetoidsOver C := twoFibreProduct F G
  change IsFibredInSetoids T.p
  exact T.property

/-- Restrict an ambient fibred-in-groupoids square to the full sub-`2`-category of categories
fibred in setoids once its apex is known to satisfy the setoid condition. -/
@[irreducible] private noncomputable def ofAmbientSquare
    {F : X ⟶ S} {G : Y ⟶ S}
    (P : BicategoricalTwoCommutativeSquare F.toHom G.toHom)
    (hsetoid : IsFibredInSetoids P.obj.p) :
    BicategoricalTwoCommutativeSquare F G :=
  let T : FibredInSetoidsOver C := ⟨P.obj, hsetoid⟩
  let p : T ⟶ X := ofAmbientHom P.p
  let q : T ⟶ Y := ofAmbientHom P.q
  let ψ : p ≫ F ≅ q ≫ G := ofAmbientIso P.ψ
  { obj := T
    p := p
    q := q
    ψ := ψ }

/-- The canonical `2`-commutative square in `FibredInSetoidsOver C`, formed by restricting the
ambient fibred-in-groupoids pullback square of `F` and `G` to the canonical setoid-valued owner
`twoFibreProduct F G`. -/
noncomputable def twoFibreProductSquare
    (F : X ⟶ S) (G : Y ⟶ S) :
    BicategoricalTwoCommutativeSquare F G :=
  ofAmbientSquare
    (FibredInGroupoidsOver.twoFibreProductSquare F.toHom G.toHom)
    (ambientTwoFibreProduct_isFibredInSetoids F G)

-- Proof sketch: reuse the ambient finality statement for the fibred-in-groupoids pullback square
-- and restrict it along the full sub-`2`-category `FibredInSetoidsOver C`.
/-- Lemma 4.39.4, owner-level form: the canonical square `twoFibreProductSquare F G` is a
bicategorical `2`-fibre product in `FibredInSetoidsOver C`. -/
theorem twoFibreProduct_isTwoFibreProduct
    (F : X ⟶ S) (G : Y ⟶ S) :
    Bicategory.IsFinal (twoFibreProductSquare F G) :=
  sorry

end FibredInSetoidsOver

end CategoryTheory
