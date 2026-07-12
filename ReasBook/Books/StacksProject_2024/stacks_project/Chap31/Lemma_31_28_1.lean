import Mathlib
import StacksProject_2024.Chap28.Definition_28_7_1

-- Declarations for this item will be appended below by the statement pipeline.

open AlgebraicGeometry
open CategoryTheory
open CategoryTheory.MonoidalCategory
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme

-- Semantic recall: `lean_leansearch` surfaced `Scheme.Modules.pullback` for module pullback and
-- the Picard/invertible-module surface; local Chapter 31 precedent uses `Scheme.Hom.fiber` and
-- `Scheme.Hom.fiberι` for scheme-theoretic fibers, and Chapter 28 provides the scheme-normality
-- owner `Scheme.isNormal`.

/-- Lemma 31.28.1: let `φ : X ⟶ Y` be a morphism of schemes and let `ℒ` be an invertible
`\mathcal O_X`-module. Assume that `X` is locally Noetherian, that `Y` is locally Noetherian,
integral, and normal, that `φ` is flat with integral fibers, that `φ` is either quasi-compact or
locally of finite type, and that `ℒ` is trivial on the generic fiber of `φ`. Then `ℒ` is pulled
back from an invertible `\mathcal O_Y`-module. -/
@[stacks 0BD7]
theorem invertibleModule_descends_of_flat_integralFibers_trivial_genericFiber
    {X Y : Scheme.{u}} (φ : X ⟶ Y)
    [IsLocallyNoetherian X] [IsLocallyNoetherian Y] [IsIntegral Y]
    (hYnormal : Y.isNormal)
    [Flat φ]
    (hfibers : ∀ y : Y, IsIntegral (Scheme.Hom.fiber φ y))
    (hqc_or_lft : QuasiCompact φ ∨ LocallyOfFiniteType φ)
    [MonoidalCategory X.Modules] [MonoidalCategory Y.Modules]
    (ℒ : X.Modules) [Functor.IsEquivalence (tensorRight ℒ)]
    (hgeneric :
      Nonempty (((Scheme.Modules.pullback (Scheme.Hom.fiberι φ (genericPoint Y))).obj ℒ) ≅
        (SheafOfModules.unit (Scheme.Hom.fiber φ (genericPoint Y)).ringCatSheaf :
          (Scheme.Hom.fiber φ (genericPoint Y)).Modules))) :
    ∃ N : Y.Modules,
      Functor.IsEquivalence (tensorRight N) ∧
        Nonempty (ℒ ≅ ((Scheme.Modules.pullback φ).obj N)) := sorry

end AlgebraicGeometry.Scheme
