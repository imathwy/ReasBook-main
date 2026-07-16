import Mathlib
import StacksProject_2024.stacks_project.Chap31.Definition_31_34_1

-- Declarations for this item will be appended below by the statement pipeline.

namespace AlgebraicGeometry

universe u

open CategoryTheory

-- Semantic recall note: `lean_leansearch` surfaced the absolute scheme owner
-- `AlgebraicGeometry.Proj`, while local Chapter 31 search showed that the project already records
-- the scheme-theoretic blowup notion through the universal-property class `IsBlowup`. Since the
-- current environment does not expose a relative-`Proj` construction on ideal sheaves, this file
-- uses that canonical owner and keeps the exceptional divisor explicit as the pulled-back center.

noncomputable section

variable (X : Scheme.{u}) (I : X.IdealSheafData)

/-- Definition 31.32.1: for a scheme `X` and a quasi-coherent ideal sheaf `I`, a blowup of `X`
in the closed subscheme defined by `I` is the scheme over `X` carrying the canonical blowup
universal property; its exceptional divisor is the inverse-image center. This uses the project's
canonical owner `IsBlowup` in place of an unavailable relative-`Proj` construction object. -/
structure Blowup extends Over X where
  /-- The structural morphism is a blowup of `X` in the center defined by `I`. -/
  isBlowup : IsBlowup hom I

namespace Blowup

/-- The underlying scheme of a blowup. -/
abbrev scheme (π : Blowup X I) : Scheme.{u} :=
  π.left

/-- A blowup carries the canonical `IsBlowup` owner on its structural morphism. -/
instance instIsBlowup (π : Blowup X I) : IsBlowup π.hom I :=
  π.isBlowup

/-- The defining blowup property carried by a blowup object. -/
theorem isBlowup_hom (π : Blowup X I) : IsBlowup π.hom I := sorry

/-- The exceptional divisor of a blowup is the inverse-image center ideal sheaf. -/
abbrev exceptionalDivisor (π : Blowup X I) : π.scheme.IdealSheafData :=
  I.comap π.hom

/-- The exceptional divisor is the pullback of the center ideal sheaf along the blowup morphism. -/
theorem exceptionalDivisor_def (π : Blowup X I) :
    π.exceptionalDivisor = I.comap π.hom :=
  rfl

end Blowup

end

end AlgebraicGeometry
