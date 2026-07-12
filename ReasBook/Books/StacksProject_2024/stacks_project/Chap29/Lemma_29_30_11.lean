import Mathlib
import StacksProject_2024.Chap29.Definition_29_30_1

-- Declarations for this item will be appended below by the statement pipeline.

open AlgebraicGeometry

universe u

namespace AlgebraicGeometry

variable {X S : Scheme.{u}} {f : X ⟶ S}

-- Semantic recall / verified owner:
-- `lean_leansearch` only surfaced the ambient scheme-morphism owners `Flat` and
-- `LocallyOfFinitePresentation`; local Chapter 29 precedent fixes the source-facing syntomic
-- owner as `Syntomic f`, and `Definition_29_30_1.lean` records a fiber over `s : S` being a local
-- complete intersection as `IsLocalCompleteIntersectionOver (S.residueField s)
-- (Scheme.Hom.fiberToSpecResidueField f s)`.

/-- Lemma 29.30.11: if `f : X ⟶ S` is flat, locally of finite presentation, and every fiber
`X_s` is a local complete intersection over the residue field `κ(s)`, then `f` is syntomic. -/
@[stacks 01UF]
theorem syntomic_of_flat_of_locallyOfFinitePresentation_of_localCompleteIntersectionFibers
    (hflat : Flat f) (hfp : LocallyOfFinitePresentation f)
    (hfiber :
      ∀ s : S,
        IsLocalCompleteIntersectionOver (S.residueField s)
          (Scheme.Hom.fiberToSpecResidueField f s)) :
    Syntomic f := sorry

end AlgebraicGeometry
