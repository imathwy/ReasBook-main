import Mathlib
import StacksProject_2024.Chap31.Definition_31_32_1

-- Declarations for this item will be appended below by the statement pipeline.

namespace AlgebraicGeometry

universe u

open CategoryTheory

-- Semantic recall: `lean_leansearch` surfaced the open-immersion restriction API
-- `IsOpenImmersion.isoRestrict`, and local Chapter 31 search confirmed that this workspace models
-- a chosen blowup through `Blowup X I` together with its explicit exceptional divisor
-- `π.exceptionalDivisor`.
--
-- The final source clause identifies `\mathcal O_{X'}(-1)` with `\mathcal O_{X'}(E)`. The
-- current project surface for blowups records only the universal-property owner `Blowup` and does
-- not yet expose a canonical blowup `\mathcal O(-1)` sheaf or a chosen `Proj` presentation, so
-- this file records the two clauses that land on existing owners without introducing a fake
-- replacement for that missing sheaf.

section

variable (X : Scheme.{u}) (I : X.IdealSheafData)

/-- Lemma 31.32.4 (1): if `π : Blowup X I` is the blowing up of `X` in the closed subscheme
defined by `I`, then the restriction of the blowup morphism to the complement of the center
support is an isomorphism. -/
@[stacks 02OS]
theorem isIso_restrict_hom_compl_support (π : Blowup X I) :
    IsIso
      (π.hom ∣_
        ⟨(I.support : Set X)ᶜ, I.support.2.isOpen_compl⟩) := sorry

/-- Lemma 31.32.4 (2): for a blowup `π : Blowup X I`, the exceptional divisor
`π.exceptionalDivisor = I.comap π.hom` is an effective Cartier divisor on the blowup scheme. -/
@[stacks 02OS]
theorem isEffectiveCartierDivisor_exceptionalDivisor (π : Blowup X I) :
    IsEffectiveCartierDivisor π.exceptionalDivisor := sorry

end

end AlgebraicGeometry
