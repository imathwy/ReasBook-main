import Mathlib
import stacks_project.Chap12.Definition_12_31_2
import stacks_project.Chap20.Lemma_20_36_1

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open CategoryTheory.Limits
open Opposite
open TopologicalSpace
open AlgebraicGeometry
open CategoryTheory.SequentialInverseSystem

noncomputable section

universe u

namespace AlgebraicGeometry.RingedSpace

variable {X : RingedSpace.{u}}

/-- The inverse system `n ↦ H^p(X, \mathcal F_n)` attached to a sequential inverse system of
`\mathcal O_X`-modules. -/
abbrev moduleCohomologyTower
    (X : RingedSpace.{u}) [HasInjectiveResolutions (SheafOfModules (RingedSpace.ringCatSheaf X))]
    (ℱ : ℕᵒᵖ ⥤ SheafOfModules (RingedSpace.ringCatSheaf X)) (p : ℕ) :
    SequentialInverseSystem (ModuleCat (globalSectionsRing X)) :=
  ℱ ⋙ (moduleGlobalSectionsFunctor X).rightDerived p

-- Proof sketch: use the short exact sequences from `stepShortExactCondition` to identify the
-- cohomology tower with the middle term in the standard short exact sequence relating the
-- principal-power quotient tower of `H^p(X, \mathcal F_1)` and the principal-power torsion tower
-- of `H^{p + 1}(X, \mathcal F_1)`. Finite length or finite generation over the Noetherian ring
-- `Γ(X, \mathcal O_X)` gives the required Mittag-Leffler control on the torsion tower, and then
-- Remark `15.94.7` transfers it to the cohomology tower.
/-- Lemma 20.36.4: if the inverse system `(\mathcal F_n)_n` of `\mathcal O_X`-modules satisfies
condition `(1)` of Lemma `20.36.1` with respect to a global section `f`, and if
`H^{p + 1}(X, \mathcal F_1)` is either of finite length over `Γ(X, \mathcal O_X)` or finite over
the Noetherian ring `Γ(X, \mathcal O_X)`, then the inverse system
`n ↦ H^p(X, \mathcal F_n)` is Mittag-Leffler. -/
theorem moduleCohomologyTower_isMittagLeffler_of_stepShortExactCondition_of_finiteLength_or_finite
    (f : StructureSheafGlobalSection X)
    (ℱ : ℕᵒᵖ ⥤ SheafOfModules (RingedSpace.ringCatSheaf X))
    (p : ℕ)
    [HasInjectiveResolutions (SheafOfModules (RingedSpace.ringCatSheaf X))]
    (hstep : stepShortExactCondition f ℱ)
    (hHp1 :
      IsFiniteLength (globalSectionsRing X)
          (moduleCohomology X (p + 1) (ℱ.obj (op 1))) ∨
        (IsNoetherianRing (globalSectionsRing X) ∧
          Module.Finite (globalSectionsRing X)
            (moduleCohomology X (p + 1) (ℱ.obj (op 1))))) :
    IsMittagLeffler (moduleCohomologyTower X ℱ p) := sorry

end AlgebraicGeometry.RingedSpace
