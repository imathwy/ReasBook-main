import Mathlib
import StacksProject_2024.stacks_project.Chap34.Lemma_34_7_9

-- Declarations for this item will be appended below by the statement pipeline.

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry
namespace Scheme

-- Semantic recall: the big `ph` site has underlying category `Scheme`, while its slice site uses
-- the canonical owner `Over S`. As in the local Chapter 34 fppf precedent, the scheme-side,
-- slice-side, and terminal-object clauses are direct recalls of the existing pullback and terminal
-- instances. The only new source-facing content here is the affine-slice pullback closure.

variable (S : Scheme.{u})

/- Lemma 34.8.13 (1): the underlying category of the big `ph` site of schemes has fibre
products. -/
#check (inferInstance : HasPullbacks Scheme)

/- Lemma 34.8.13 (2): the evident functor from the underlying category of a big `ph` site to the
category of all schemes commutes with fibre products. -/
#check (inferInstance : PreservesLimitsOfShape WalkingCospan (𝟭 Scheme))

/- Lemma 34.8.13 (3): the underlying category of the slice `(\mathit{Sch}/S)_{ph}` has fibre
products. -/
#check (inferInstance : HasPullbacks (Over S))

/- Lemma 34.8.13 (4): the evident functor `(\mathit{Sch}/S)_{ph} ⥤ \mathit{Sch}` commutes with
taking fibre products. -/
#check (inferInstance : PreservesLimitsOfShape WalkingCospan (Over.forget S))

/- Lemma 34.8.13 (5): the underlying category of the affine slice site
`(\textit{Aff}/S)_{ph}` has fibre products. -/
#check (inferInstance : HasPullbacks (Scheme.AffineOver S))

/- Lemma 34.8.13 (6): the evident functor `(\textit{Aff}/S)_{ph} ⥤ \mathit{Sch}` commutes with
taking fibre products. -/
#check
  (inferInstance :
    PreservesLimitsOfShape WalkingCospan (Scheme.AffineOver.forget S ⋙ Over.forget S))

/- Lemma 34.8.13 (7): the slice site `(\mathit{Sch}/S)_{ph}` has final object `S/S`, realized as
the identity morphism `𝟙 S : S ⟶ S`. -/
#check (Over.mkIdTerminal : Limits.IsTerminal (Over.mk (𝟙 S)))

end Scheme
end AlgebraicGeometry
