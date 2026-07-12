import Mathlib
import StacksProject_2024.Chap29.Definition_29_40_1

-- Declarations for this item will be appended below by the statement pipeline.

open AlgebraicGeometry
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry

/- Semantic recall / owner check:
`Definition_29_40_1.lean` already provides the chapter owners `QuasiProjective`,
`HQuasiProjective`, and `LocallyQuasiProjective`, while `Definition_29_15_1.lean` provides the
scheme-side owner `Scheme.Hom.FiniteType`. This lemma file therefore keeps only the source-facing
consequences from Lemma 29.40.4, stated against those canonical owners. -/

section

variable {X S : Scheme.{u}} {f : X ⟶ S}

/-- Lemma 29.40.4 (1): a quasi-projective morphism is separated. -/
@[stacks 01VU]
theorem QuasiProjective.isSeparated [QuasiProjective f] :
    IsSeparated f := sorry

/-- Lemma 29.40.4 (2): a quasi-projective morphism is of finite type. -/
@[stacks 01VU]
theorem QuasiProjective.finiteType [QuasiProjective f] :
    Scheme.Hom.FiniteType f := sorry

/-- Lemma 29.40.4 (3): an H-quasi-projective morphism is separated. -/
@[stacks 01VU]
theorem HQuasiProjective.isSeparated [HQuasiProjective f] :
    IsSeparated f := sorry

/-- Lemma 29.40.4 (4): an H-quasi-projective morphism is of finite type. -/
@[stacks 01VU]
theorem HQuasiProjective.finiteType [HQuasiProjective f] :
    Scheme.Hom.FiniteType f := sorry

/-- Lemma 29.40.4 (5): a locally quasi-projective morphism is separated. -/
@[stacks 01VU]
theorem LocallyQuasiProjective.isSeparated [LocallyQuasiProjective f] :
    IsSeparated f := sorry

/-- Lemma 29.40.4 (6): a locally quasi-projective morphism is locally of finite type. -/
@[stacks 01VU]
theorem LocallyQuasiProjective.locallyOfFiniteType [LocallyQuasiProjective f] :
    LocallyOfFiniteType f := sorry

end

end AlgebraicGeometry
