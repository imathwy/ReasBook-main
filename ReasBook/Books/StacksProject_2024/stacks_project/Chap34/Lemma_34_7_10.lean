import Mathlib.CategoryTheory.Limits.Constructions.Over.Products
import StacksProject_2024.stacks_project.Chap34.Lemma_34_7_9

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open CategoryTheory.Limits
open AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme

-- Semantic recall: the underlying category of the big fppf site is just `Scheme`, so the scheme-
-- and slice-side clauses are all canonical owner facts: pullbacks on `Scheme`, pullbacks on
-- `Over S`, preservation of pullbacks by the identity and forgetful functors, and the terminal
-- slice object `Over.mkIdTerminal`. The only genuinely source-facing new clause is the affine-slice
-- pullback closure, which is not a bare recall because it depends on the affine-over owner from
-- Definition 34.7.8 and the pullback instance established in Lemma 34.7.9.

variable (S : Scheme.{u})

/- Lemma 34.7.10: the source clauses for `\mathit{Sch}_{fppf}` are the canonical facts that
`Scheme` has pullbacks and that the identity functor on `Scheme` preserves them. -/
#check (inferInstance : HasPullbacks Scheme)
#check (inferInstance : PreservesLimitsOfShape WalkingCospan (𝟭 Scheme))

/- Lemma 34.7.10 (1): the underlying category of `(Sch/S)_{fppf}` has fibre products. -/
#check (inferInstance : HasPullbacks (Over S))

/- Lemma 34.7.10 (2): the obvious functor `(Sch/S)_{fppf} ⥤ Sch` commutes with fibre products. -/
#check (inferInstance : PreservesLimitsOfShape WalkingCospan (Over.forget S))

/- Lemma 34.7.10 (3): the underlying category of `(Aff/S)_{fppf}` has fibre products. -/
#check (inferInstance : HasPullbacks (Scheme.AffineOver S))

/- Lemma 34.7.10 (4): the obvious functor `(Aff/S)_{fppf} ⥤ Sch` commutes with fibre products. -/
#check
  (inferInstance :
    PreservesLimitsOfShape WalkingCospan (Scheme.AffineOver.forget S ⋙ Over.forget S))

/- Lemma 34.7.10 (5): the object `S/S` is a final object of `(Sch/S)_{fppf}`. -/
#check (Over.mkIdTerminal : IsTerminal (Over.mk (𝟙 S)))

end AlgebraicGeometry.Scheme
