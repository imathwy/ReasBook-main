import Mathlib
import StacksProject_2024.Chap28.Lemma_28_24_2

-- Declarations for this item will be appended below by the statement pipeline.

open AlgebraicGeometry
open CategoryTheory

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Modules

variable {X Y : Scheme.{u}}
variable [MonoidalCategory (SheafOfModules X.ringCatSheaf)]
variable [MonoidalClosed (SheafOfModules X.ringCatSheaf)]
variable [MonoidalCategory (SheafOfModules Y.ringCatSheaf)]
variable [MonoidalClosed (SheafOfModules Y.ringCatSheaf)]

-- Semantic recall: `lean_leansearch` surfaced the canonical owners
-- `Scheme.IdealSheafData.comap` and `Scheme.Modules.pushforward`; Lemma `28.24.2` already fixes
-- the annihilator subsheaf owner as `idealTorsionSubsheaf`, so this item is best stated as the
-- equality of the pushed-forward source annihilator image with the target annihilator image.

/-- Lemma 28.24.4: let `f : X ⟶ Y` be quasi-compact and quasi-separated, let `I` be a finite type
quasi-coherent ideal sheaf on `Y`, and let `ℱ` be a quasi-coherent `\mathcal O_X`-module. Then
the pushforward of the subsheaf of `ℱ` annihilated by `I.comap f` is, sectionwise on every open
of `Y`, exactly the subsheaf of `f_* ℱ` annihilated by `I`. -/
@[stacks 07ZN]
theorem range_pushforward_idealTorsionSubsheafι_app_eq
    (f : X ⟶ Y) [QuasiCompact f] [QuasiSeparated f]
    (I : Y.IdealSheafData)
    [((show Y.Modules from Subobject.underlying.obj (idealSheafSubobject I)).IsFiniteType)]
    (ℱ : X.Modules) [ℱ.IsQuasicoherent]
    (U : Y.Opens) :
    Set.range (Hom.app
        ((pushforward f).map (idealTorsionSubsheafι (I.comap f) ℱ)) U) =
      Set.range (Hom.app
        (idealTorsionSubsheafι I ((pushforward f).obj ℱ)) U) := sorry

end AlgebraicGeometry.Scheme.Modules
