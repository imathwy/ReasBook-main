import Mathlib.CategoryTheory.Monoidal.Closed.Cartesian
import stacks_project.Chap20.Lemma_20_42_2

-- Declarations for this item will be appended below by the statement pipeline.

open AlgebraicGeometry
open CategoryTheory
open CategoryTheory.MonoidalCategory
open CategoryTheory.MonoidalClosed
open scoped CartesianClosed

noncomputable section

universe u

attribute [local instance] HasDerivedCategory.standard

namespace AlgebraicGeometry.RingedSpace

/- Domain-style sampling for Lemma 20.42.5:
- primary domain: internal-Hom composition in a braided monoidal closed derived category of
  `\mathcal O_X`-modules;
- inspected owner declarations:
  `AlgebraicGeometry.RingedSpace.RingedSpaceDerived`,
  `CategoryTheory.ihom`,
  `CategoryTheory.MonoidalClosed.comp`,
  `CategoryTheory.ihom.ev`,
  `CategoryTheory.MonoidalClosed.curry`;
- best owner abstraction: the closed-monoidal composition morphism `comp K L M` on the ambient
  owner `RingedSpaceDerived X`, together with the standard internal-Hom notation `K ⟹ L`;
- primitive data: the braided monoidal closed structure on `RingedSpaceDerived X` and the three
  objects `K`, `L`, `M`;
- derived API: the Stacks-ordered comparison map obtained by braiding the two internal-Hom factors
  into the order expected by `comp K L M`.

Source/core/bridge triage:
- `source-facing`: the chapter-level morphism
  `R\mathcal H\!\mathit{om}(L, M) \otimes^{\mathbf L} R\mathcal H\!\mathit{om}(K, L) ⟶
    R\mathcal H\!\mathit{om}(K, M)`;
- `core/canonical`: the ambient internal-Hom owner notation `K ⟹ L` and the composition morphism
  `comp K L M`;
- `bridge/view`: the braiding that swaps the Stacks Project factor order into mathlib's canonical
  order for `comp`.

This item is therefore a `source-facing` bridge built directly from the `core/canonical` owner
data, so the public API should expose the standard internal-Hom notation and the shortest
unambiguous owner form `comp K L M`, rather than raw `(ihom _).obj _` terms or redundant namespace
scaffolding. Downstream constructions that do not need the Stacks-ordered factor swap should call
`comp K L M` directly.
-/

section

variable {X : RingedSpace.{u}}

variable [MonoidalCategory (RingedSpaceDerived X)]
variable [BraidedCategory (RingedSpaceDerived X)]
variable [MonoidalClosed (RingedSpaceDerived X)]

/-- Lemma 20.42.5: for `K`, `L`, and `M` in `D(\mathcal O_X)`, there is a canonical morphism
`R\mathcal H\!\mathit{om}(L, M) \otimes_{\mathcal O_X}^{\mathbf L}
R\mathcal H\!\mathit{om}(K, L) \to R\mathcal H\!\mathit{om}(K, M)`, functorial in `K`, `L`, and
`M`. In the closed monoidal structure on `D(\mathcal O_X)`, this is the usual internal-Hom
composition morphism after swapping the two factors into mathlib's order. -/
noncomputable def internalHomComposition
    (K L M : RingedSpaceDerived X) :
    (L ⟹ M) ⊗ (K ⟹ L) ⟶ (K ⟹ M) :=
  (β_ (L ⟹ M) (K ⟹ L)).hom ≫ comp K L M

end

end AlgebraicGeometry.RingedSpace
