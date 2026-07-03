import Mathlib
import StacksProject_2024.Chap13.Lemma_13_15_4
import StacksProject_2024.Chap17.Lemma_17_17_6

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry
open TopCat
open TopologicalSpace

noncomputable section

universe u

namespace AlgebraicGeometry.RingedSpace.ModuleSheaf

variable {X : RingedSpace.{u}}

/-
Domain-style sampling for Lemma 17.17.7:
- primary domain: epimorphic generators of `X.Modules` by the lower-shriek structure modules
  `j_{U!}\mathcal O_U`, together with the resulting `ObjectProperty` package used in the Chapter 13
  truncation-resolution formalism;
- sampled owner declarations:
  `RingedSpace.Modules`,
  `structureSheafLowerShriek`,
  `CategoryTheory.ObjectProperty.HasEpiCover`,
  `CategoryTheory.exists_upperTruncationResolutionTower`;
- best owner abstraction: the ambient owner is the canonical module category `X.Modules`; the
  source-facing summands are the already-defined objects `structureSheafLowerShriek U`, and the
  closure/cover statements should be expressed directly as an `ObjectProperty` on `X.Modules`
  rather than via a parallel wrapper category;
- primitive data: an index type `I`, a family of opens `U : I → Opens X.carrier`, and an
  epimorphism from the coproduct of the corresponding modules `j_{U_i!}\mathcal O_{U_i}`;
- derived API: the object property of being such a coproduct, its `ContainsZero` /
  `IsClosedUnderFiniteCoproducts` / `HasEpiCover` instances, and the flat quotient corollary.

Source/core/bridge triage:
- `source-facing`: the coproduct and flat epimorphic presentations of an `\mathcal O_X`-module;
- `core/canonical`: `X.Modules`, `structureSheafLowerShriek`, and the generic
  `CategoryTheory.ObjectProperty` closure classes;
- `bridge/view`: none beyond the source-facing `structureSheafLowerShriek` owner from
  `Lemma_17_17_6`.
-/

local notation "ModX" => X.Modules

-- Proof sketch: for every open `U ⊆ X` and section `s ∈ ℱ(U)`, the adjunction between
-- restriction to `U` and extension by zero gives a morphism `j_{U!}\mathcal O_U ⟶ ℱ` sending `1`
-- to `s`. Taking the coproduct over all pairs `(U, s)` yields a morphism whose stalk maps are
-- surjective, hence the morphism is epimorphic.
/-- Lemma 17.17.7 (1): any sheaf of `\mathcal O_X`-modules is the quotient of a direct sum of
lower-shriek structure sheaves `j_{U_i!}\mathcal O_{U_i}`. -/
theorem exists_epi_from_coproduct_openSubsetStructureSheafLowerShriek
    (ℱ : ModX) :
    ∃ (I : Type u) (U : I → Opens X.carrier)
      (φ : (∐ fun i : I ↦ structureSheafLowerShriek (U i)) ⟶ ℱ), Epi φ := sorry

/-- The object property on `\mathrm{Mod}(\mathcal O_X)` saying that a module is a direct sum,
equivalently a categorical coproduct, of lower-shriek structure sheaves `j_{U!}\mathcal O_U`. -/
def isCoproductOfOpenSubsetStructureSheafLowerShrieks
    (X : RingedSpace.{u}) : CategoryTheory.ObjectProperty X.Modules :=
  fun ℱ ↦
    ∃ (I : Type u) (U : I → Opens X.carrier),
      Nonempty (ℱ ≅ ∐ fun i : I ↦ structureSheafLowerShriek (U i))

/-- The zero `\mathcal O_X`-module is the empty coproduct of lower-shriek structure sheaves. -/
instance isCoproductOfOpenSubsetStructureSheafLowerShrieks_containsZero :
    (isCoproductOfOpenSubsetStructureSheafLowerShrieks X).ContainsZero := sorry

/-- Finite coproducts of coproducts of lower-shriek structure sheaves are again coproducts of
lower-shriek structure sheaves. -/
instance isCoproductOfOpenSubsetStructureSheafLowerShrieks_isClosedUnderFiniteCoproducts :
    (isCoproductOfOpenSubsetStructureSheafLowerShrieks X).IsClosedUnderFiniteCoproducts := sorry

/-- Every `\mathcal O_X`-module admits an epimorphism from a coproduct of lower-shriek structure
sheaves `j_{U!}\mathcal O_U`. -/
instance isCoproductOfOpenSubsetStructureSheafLowerShrieks_hasEpiCover :
    CategoryTheory.ObjectProperty.HasEpiCover
      (isCoproductOfOpenSubsetStructureSheafLowerShrieks X) := sorry

-- Proof sketch: apply the epimorphic coproduct presentation from `(1)` and use that each summand
-- `j_{U_i!}\mathcal O_{U_i}` is flat by `structureSheafLowerShriek_isFlat`. Then apply
-- the earlier direct-sum flatness result to conclude that the source coproduct is flat.
/-- Lemma 17.17.7 (2): any sheaf of `\mathcal O_X`-modules is the quotient of a flat
`\mathcal O_X`-module. -/
theorem exists_epi_from_flat
    (ℱ : ModX) :
    ∃ (𝒢 : ModX)
      (h𝒢 : SheafOfModules.RingedSite.IsFlat X.sheaf 𝒢) (φ : 𝒢 ⟶ ℱ), Epi φ := sorry

end AlgebraicGeometry.RingedSpace.ModuleSheaf
