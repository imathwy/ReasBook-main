import Mathlib
import StacksProject_2024.stacks_project.Chap05.Definition_5_11_4
import StacksProject_2024.stacks_project.Chap05.Definition_5_20_1
import StacksProject_2024.stacks_project.Chap05.Definition_5_9_1

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory TopologicalSpace

universe u

variable {X : Type u} [TopologicalSpace X]

/- Domain-style sampling for Remark 5.20.5:
- primary domain: dimension functions on topological spaces and first sheaf cohomology of the
  constant integer sheaf
- same-domain declarations inspected:
  `IsDimensionFunction` in `Definition_5_20_1`
  `IsDimensionFunction.isLocallyConstant_sub` in `Lemma_5_20_3`
  `exists_open_neighborhood_with_dimensionFunction` in `Lemma_5_20_4`
  direct `H 1` owner usage in `TopologicalSpace.SheafCohomology.squareZeroBoundaryClass`

Owner-abstraction choice:
- `source-facing`: the obstruction-class existence statement of the remark
- `core/canonical`: `IsDimensionFunction` and the canonical cohomology object
  `((constantSheaf (Opens.grothendieckTopology X) AddCommGrpCat).obj
    (AddCommGrpCat.of (ULift ℤ))).H 1`
- `bridge/view`: the vanishing criterion relating a cohomology class to a global dimension
  function

Primitive data versus derived API:
- primitive data already lives in the upstream owner `IsDimensionFunction` and in the local
  existence/difference lemmas `Lemma_5_20_3` and `Lemma_5_20_4`
- this file should therefore contribute only the derived cohomological existence statement, not a
  parallel local alias for the canonical `H^1` type or for its vanishing specification
-/

-- Proof sketch: Lemma 5.20.4 gives local dimension functions on a catenary locally Noetherian
-- sober space, and Lemma 5.20.3 identifies the differences of two such local functions on overlaps
-- with locally constant integer-valued functions. These transition functions define a Cech
-- 1-cocycle for the constant integer sheaf, hence an obstruction class in `H^1(X, \underline Z)`;
-- its vanishing is equivalent to gluing the local dimension functions to a global one.
/-- Remark 5.20.5: on a catenary, locally Noetherian, sober topological space, there exists an
obstruction class in `H^1(X, \underline{\mathbf Z})` to the existence of a global dimension
function. Here sobriety is encoded canonically by `T₀` and quasi-sobriety. -/
theorem exists_dimensionFunction_obstruction_class
    [LocallyNoetherianSpace X] [T0Space X] [QuasiSober X] [CatenarySpace X]
    [HasSheafify (Opens.grothendieckTopology X) AddCommGrpCat]
    [HasExt (Sheaf (Opens.grothendieckTopology X) AddCommGrpCat)] :
    ∃ c : ((constantSheaf (Opens.grothendieckTopology X) AddCommGrpCat).obj
      (AddCommGrpCat.of (ULift ℤ))).H 1,
      c = 0 ↔ ∃ δ : X → ℤ, IsDimensionFunction δ :=
  sorry
