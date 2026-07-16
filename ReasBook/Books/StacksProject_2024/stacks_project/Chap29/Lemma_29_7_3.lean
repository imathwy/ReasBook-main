import Mathlib
import StacksProject_2024.stacks_project.Chap29.Definition_29_7_1

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory

namespace AlgebraicGeometry

universe u

-- Semantic recall: `lean_leansearch` surfaced the canonical scheme-theoretic-image owner
-- `Scheme.Hom.image`; local Chapter 29 inspection confirmed `schemeTheoreticClosure` and
-- `schemeTheoreticallyDense` as the project owners from `Definition_29_7_1`.
-- The Stacks tag evidence is consistent: item tag `01RD` matches the source URL `/tag/01RD`.

variable {X : Scheme.{u}}

/-- Lemma 29.7.3: if the inclusion morphism of an open subscheme `U ⊆ X` is quasi-compact, then
`U` is scheme theoretically dense in `X` if and only if its scheme theoretic closure in `X` is
all of `X`. -/
@[stacks 01RD]
theorem schemeTheoreticallyDense_iff_schemeTheoreticClosure_eq_self
    (U : X.Opens) [QuasiCompact U.ι] :
    schemeTheoreticallyDense U ↔ schemeTheoreticClosure U = X := sorry

end AlgebraicGeometry
