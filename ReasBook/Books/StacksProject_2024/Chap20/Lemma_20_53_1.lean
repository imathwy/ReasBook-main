import Mathlib
import stacks_project.Chap13.Definition_13_37_1
import stacks_project.Chap17.Definition_17_8_1
import stacks_project.Chap17.Lemma_17_17_6
import stacks_project.Chap20.Lemma_20_15_1

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open CategoryTheory.Limits
open Opposite
open TopologicalSpace
open AlgebraicGeometry

noncomputable section

universe u v

attribute [local instance] HasDerivedCategory.standard

namespace AlgebraicGeometry.RingedSpace

section

variable {X : RingedSpace.{u}} (U : Opens X.carrier)
variable [HasSheafify (Opens.grothendieckTopology X.carrier) AddCommGrpCat.{u}]
variable [HasExt.{u} (Sheaf (Opens.grothendieckTopology X.carrier) AddCommGrpCat.{u})]
variable [IsGrothendieckAbelian.{v} (RingedSpace.Modules X)]

local notation "ModX" => (RingedSpace.Modules X)
local notation "single0" => DerivedCategory.singleFunctor ModX (0 : ℤ)

/- Domain-style sampling for Lemma 20.53.1:
- primary domain: compact objects in `D(\mathcal O_X)` detected by objectwise sheaf cohomology on
  an open subset via extension by zero;
- sampled owner declarations:
  `CategoryTheory.IsCompactObject`,
  `ModuleSheaf.structureSheafLowerShriek`,
  `moduleUnderlyingSheaf`,
  `Sheaf.cohomologyPresheafFunctor`;
- best owner abstraction: the core owner is `IsCompactObject` on the derived category
  `DerivedCategory (RingedSpace.Modules X)`; the source-facing object is
  `ModuleSheaf.structureSheafLowerShriek U`, and objectwise cohomology over `U` is a
  bridge computed from `moduleUnderlyingSheaf X` and `Sheaf.cohomologyPresheafFunctor`;
- primitive data: the open subset `U`, the uniform vanishing bound, and the direct-sum
  compatibility of the objectwise cohomology functors;
- derived API: compactness of the degree-zero derived object attached to `j_{U!}\mathcal O_U`.

Source/core/bridge triage:
- `source-facing`: the compactness statement for `j_{U!}\mathcal O_U[0]`;
- `core/canonical`: `CategoryTheory.IsCompactObject`;
- `bridge/view`: objectwise cohomology on `U` via `moduleUnderlyingSheaf X`.
-/

private abbrev moduleObjectwiseCohomologyFunctor (p : ℕ) :
    ModX ⥤ AddCommGrpCat.{u} :=
  moduleUnderlyingSheaf X ⋙
    Sheaf.cohomologyPresheafFunctor (Opens.grothendieckTopology X.carrier) p ⋙
      (evaluation (Opens X.carrier)ᵒᵖ AddCommGrpCat.{u}).obj (op U)

private abbrev moduleObjectwiseCohomology (p : ℕ) (ℱ : ModX) :
    AddCommGrpCat.{u} :=
  (moduleObjectwiseCohomologyFunctor U p).obj ℱ

-- Proof sketch: identify `Hom_{D(\mathcal O_X)}(j_! \mathcal O_U, -)` with `R\Gamma(U, -)` using
-- the extension-by-zero adjunction. The bound on ordinary cohomology and the hypothesis that each
-- `H^p(U, -)` commutes with direct sums imply that `R\Gamma(U, -)` commutes with direct sums by
-- computing on K-injective representatives, hence the representing object `j_! \mathcal O_U[0]`
-- is compact.
/-- Lemma 20.53.1: if there exists an integer bound above which the cohomology groups
`H^p(U, \mathcal F)` vanish for every `\mathcal O_X`-module `\mathcal F`, and if each
cohomology functor `\mathcal F \mapsto H^p(U, \mathcal F)` commutes with arbitrary direct sums,
then `j_! \mathcal O_U`, viewed as an object of `D(\mathcal O_X)` concentrated in degree `0`, is
a compact object. -/
theorem openSubsetStructureSheafExtensionByZero_isCompactObject_of_finiteCohomologicalDimension_and_directSumCompatibility
    (hvanish :
      ∃ d : ℤ,
        ∀ (p : ℕ), d < p → ∀ ℱ : ModX,
          IsZero (moduleObjectwiseCohomology U p ℱ))
    (hdirect :
      ∀ (p : ℕ) (ι : Type u),
        PreservesColimitsOfShape (Discrete ι) (moduleObjectwiseCohomologyFunctor U p)) :
    IsCompactObject ((single0).obj (ModuleSheaf.structureSheafLowerShriek U)) := sorry

end

end AlgebraicGeometry.RingedSpace
