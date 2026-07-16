import Mathlib
import StacksProject_2024.stacks_project.Chap04.Definition_4_38_3
import StacksProject_2024.stacks_project.Chap04.Lemma_4_35_7

-- Declarations for this item will be appended below by the statement pipeline.

universe v u

namespace CategoryTheory

open CategoryOver
open FibredInSetsOver

variable {C : Type u} [Category.{v} C]
variable {X Y S : FibredInSetsOver C}

/-- The explicit ambient `2`-fibre product of the underlying based functors of `F` and `G`. -/
private noncomputable abbrev explicitTwoFibreProductOver
    (F : X ⟶ S) (G : Y ⟶ S) :=
  explicitTwoFibreProduct (toBasedFunctor F) (toBasedFunctor G)

/- Domain-style sampling for Lemma 4.38.4:
- primary domain: categories fibred in sets over a fixed base and their explicit `2`-fibre
  products in `Cat/C`;
- inspected owner-level declarations:
  `IsFibredInSets`,
  `FibredInSetsOver`,
  `FibredInSetsOver.ofAmbientHom`,
  `FibredInSetsOver.ofAmbientIso`,
  `FibredInGroupoidsOver.twoFibreProduct`,
  `FibredInGroupoidsOver.twoFibreProductSquare`,
  `FibredInGroupoidsOver.twoFibreProduct_isTwoFibreProduct`,
  `explicitTwoFibreProductProjection_isFibredInGroupoids`;
- best owner abstraction: the source-facing owner lives in `FibredInSetsOver C`, obtained by
  rebundling the ambient chapter owner `FibredInGroupoidsOver.twoFibreProduct`; the explicit
  pullback projection theorem is the closure bridge needed to upgrade the ambient apex from
  groupoids to sets.

Primitive-vs-derived split:
- primitive source-facing data: the morphisms `F : X ⟶ S` and `G : Y ⟶ S`;
- derived API: the fibred-in-sets closure theorem on the explicit pullback projection, together
  with the rebundled owner object `FibredInSetsOver.twoFibreProduct`, the canonical square, and
  the inherited finality theorem.

Source/core/bridge triage:
- `source-facing`: `FibredInSetsOver.twoFibreProductSquare` and
  `FibredInSetsOver.twoFibreProduct_isTwoFibreProduct`;
- `core/canonical`: `FibredInGroupoidsOver.twoFibreProductSquare` and
  `FibredInGroupoidsOver.twoFibreProduct_isTwoFibreProduct`;
- `bridge/view`: `explicitTwoFibreProductProjection_isFibredInSets`, which upgrades the ambient
  explicit pullback projection from the fibred-in-groupoids owner to the fibred-in-sets setting,
  enabling the owner-level rebundling in `FibredInSetsOver C`. -/

-- Proof sketch: the underlying projection of the explicit `2`-fibre product is fibred in
-- groupoids by Lemma `4.35.7`, since categories fibred in sets are in particular fibred in
-- groupoids. For discreteness, identify each fiber with the corresponding `2`-fibre product of
-- the discrete fibers of `X` and `Y` over a fixed base object and check that this fiber is again
-- discrete.
/-- Lemma 4.38.4: if `F : X ⟶ S` and `G : Y ⟶ S` are morphisms of categories fibred in sets over
`C`, then the explicit `2`-fibre-product projection from Lemma 4.32.3 is again fibred in sets
over `C`. Hence the `2`-category of categories fibred in sets over `C` has `2`-fibre products
described by the same construction. -/
theorem explicitTwoFibreProductProjection_isFibredInSets
    (F : X ⟶ S) (G : Y ⟶ S) :
    IsFibredInSets (explicitTwoFibreProductOver F G).p :=
  sorry

/-- The explicit `2`-fibre-product projection carries the canonical fibred-in-sets structure. -/
instance (F : X ⟶ S) (G : Y ⟶ S) :
    IsFibredInSets (explicitTwoFibreProductOver F G).p :=
  explicitTwoFibreProductProjection_isFibredInSets F G

namespace FibredInSetsOver

/-- The ambient fibred-in-groupoids pullback also satisfies the fibred-in-sets condition. -/
-- Proof sketch: identify the projection of `FibredInGroupoidsOver.twoFibreProduct F.toHom G.toHom`
-- with the explicit pullback projection `explicitTwoFibreProductOver F G` and reuse
-- `explicitTwoFibreProductProjection_isFibredInSets`.
private theorem ambientTwoFibreProduct_isFibredInSets
    (F : X ⟶ S) (G : Y ⟶ S) :
    IsFibredInSets (FibredInGroupoidsOver.twoFibreProduct F.toHom G.toHom).p := by
  change IsFibredInSets (explicitTwoFibreProductOver F G).p
  exact explicitTwoFibreProductProjection_isFibredInSets F G

/-- The canonical fibred `2`-fibre product of morphisms of categories fibred in sets over `C`. -/
noncomputable abbrev twoFibreProduct
    (F : X ⟶ S) (G : Y ⟶ S) :
    FibredInSetsOver C :=
  ⟨FibredInGroupoidsOver.twoFibreProduct F.toHom G.toHom,
    ambientTwoFibreProduct_isFibredInSets F G⟩

/-- Restrict an ambient fibred-in-groupoids square to the full sub-`2`-category of categories
fibred in sets, once its apex is known to be fibred in sets. -/
@[irreducible] private noncomputable def ofFibredInGroupoidsSquare
    {F : X ⟶ S} {G : Y ⟶ S}
    (P : BicategoricalTwoCommutativeSquare F.toHom G.toHom)
    (hsets : IsFibredInSets P.obj.p) :
    BicategoricalTwoCommutativeSquare F G :=
  let T : FibredInSetsOver C := ⟨P.obj, hsets⟩
  let p : T ⟶ X := ofAmbientHom P.p
  let q : T ⟶ Y := ofAmbientHom P.q
  let ψ : p ≫ F ≅ q ≫ G := ofAmbientIso P.ψ
  { obj := T
    p := p
    q := q
    ψ := ψ }

/-- The canonical `2`-commutative square in `FibredInSetsOver C`, formed by the ambient
fibred-in-groupoids pullback owner of `F` and `G`. -/
noncomputable def twoFibreProductSquare
    (F : X ⟶ S) (G : Y ⟶ S) :
    BicategoricalTwoCommutativeSquare F G :=
  ofFibredInGroupoidsSquare
    (FibredInGroupoidsOver.twoFibreProductSquare F.toHom G.toHom)
    (ambientTwoFibreProduct_isFibredInSets F G)

-- Proof sketch: use the ambient `2`-fibre-product universal property in
-- `FibredCategoryOver C`, then observe that every induced factorization lands back in the full
-- sub-`2`-category `FibredInSetsOver C` because the apex constructed above is fibred in sets.
/-- The canonical square `twoFibreProductSquare F G` is a bicategorical `2`-fibre product in
`FibredInSetsOver C`. -/
theorem twoFibreProduct_isTwoFibreProduct
    (F : X ⟶ S) (G : Y ⟶ S) :
    Bicategory.IsFinal (twoFibreProductSquare F G) :=
  sorry

end FibredInSetsOver

end CategoryTheory
