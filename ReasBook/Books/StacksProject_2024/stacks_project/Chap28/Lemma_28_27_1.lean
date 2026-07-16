import StacksProject_2024.stacks_project.Chap28.Definition_28_26_1

-- Declarations for this item will be appended below by the statement pipeline.

open AlgebraicGeometry
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Modules

-- Semantic recall: `lean_leansearch` returned the canonical scheme-side owner
-- `Scheme.IsQuasiAffine`; the Chapter 28 local owner for ampleness is
-- `Scheme.Modules.IsAmple`. The structure sheaf is represented as the unit
-- `SheafOfModules.unit X.ringCatSheaf`.

/-- The structure sheaf, viewed as the unit `\mathcal O_X`-module, carries the standard
invertible-module interface whose tensor powers are again the unit module and whose nonvanishing
opens are the usual scheme-theoretic basic opens. -/
instance structureSheafInvertible (X : Scheme.{u}) :
    Invertible (SheafOfModules.unit X.ringCatSheaf) where
  isEquivalence_tensorRight := inferInstance

end AlgebraicGeometry.Scheme.Modules

namespace AlgebraicGeometry.Scheme

/-- Lemma 28.27.1: a scheme `X` is quasi-affine if and only if its structure sheaf
`\mathcal O_X` is ample. -/
@[stacks 01QE]
theorem isQuasiAffine_iff_structureSheaf_isAmple (X : Scheme.{u}) :
    X.IsQuasiAffine ↔ Modules.IsAmple (SheafOfModules.unit X.ringCatSheaf) := sorry

end AlgebraicGeometry.Scheme
