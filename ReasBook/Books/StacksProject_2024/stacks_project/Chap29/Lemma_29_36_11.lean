import Mathlib
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.

open AlgebraicGeometry

-- Semantic recall: `lean_leansearch` recovered the scheme-side owner `Etale`, and a direct mathlib
-- source check shows that `AlgebraicGeometry.Etale.iff_flat_and_formallyUnramified` exposes the
-- `LocallyOfFinitePresentation` clause. The item is therefore a pure canonical recall.

/- Lemma 29.36.11: an étale morphism is locally of finite presentation. This is a pure canonical
recall: mathlib packages the relevant clause in
`AlgebraicGeometry.Etale.iff_flat_and_formallyUnramified`, and the instance is available directly
by typeclass inference. -/
recall AlgebraicGeometry.Etale.iff_flat_and_formallyUnramified

section

variable {X S : Scheme} (f : X ⟶ S) [Etale f]

#check (inferInstance : LocallyOfFinitePresentation f)

end
