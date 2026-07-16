import Mathlib.CategoryTheory.Limits.Constructions.Over.Products
import StacksProject_2024.stacks_project.Chap34.Definition_34_4_8

open CategoryTheory
open CategoryTheory.Limits
open AlgebraicGeometry

universe u

namespace AlgebraicGeometry
namespace Scheme

/- Semantic recall: the big étale site has underlying category `Scheme`; the big and small slice
owners are the canonical `Over S` and `S.Etale`; and `Definition_34_4_8` already fixes the affine
étale owners `S.AffineOver` and `smallAffineEtaleSite S`. Hence the source clauses here are
direct recalls of the existing pullback-preservation and terminal-object owners, rather than new
wrapper declarations. -/

variable (S : Scheme.{u})

/- Lemma 34.4.10 (1): the underlying category of the big étale site has fibre products. -/
#check (inferInstance : HasPullbacks Scheme)

/- Lemma 34.4.10 (2): the obvious functor from the big étale site to `Sch` preserves fibre
products. -/
#check (inferInstance : PreservesLimitsOfShape WalkingCospan (𝟭 Scheme))

/- Lemma 34.4.10 (3): the underlying category of `(\mathit{Sch}/S)_{\acute{e}tale}` has fibre
products. -/
#check (inferInstance : HasPullbacks (Over S))

/- Lemma 34.4.10 (4): the obvious functor `(\mathit{Sch}/S)_{\acute{e}tale} ⥤ \mathit{Sch}`
preserves fibre products. -/
#check (inferInstance : PreservesLimitsOfShape WalkingCospan (Over.forget S))

/- Lemma 34.4.10 (5): the underlying category of the small étale site `S_{\acute{e}tale}` has
fibre products. -/
#check (inferInstance : HasPullbacks S.Etale)

/- Lemma 34.4.10 (6): the obvious functor `S_{\acute{e}tale} ⥤ \mathit{Sch}` preserves fibre
products. -/
#check (inferInstance : PreservesLimitsOfShape WalkingCospan (smallEtaleToScheme S))

/- Lemma 34.4.10 (7): the underlying category of `(\textit{Aff}/S)_{\acute{e}tale}` has fibre
products. -/
#check (inferInstance : HasPullbacks S.AffineOver)

/- Lemma 34.4.10 (8): the obvious functor `(\textit{Aff}/S)_{\acute{e}tale} ⥤ \mathit{Sch}`
preserves fibre products. -/
#check (inferInstance : PreservesLimitsOfShape WalkingCospan (bigAffineEtaleToScheme S))

/- Lemma 34.4.10 (9): the underlying category of `S_{affine, {\acute{e}tale}}` has fibre
products. -/
#check (inferInstance : HasPullbacks (smallAffineEtaleSite S))

/- Lemma 34.4.10 (10): the obvious functor `S_{affine, {\acute{e}tale}} ⥤ \mathit{Sch}`
preserves fibre products. -/
#check (inferInstance : PreservesLimitsOfShape WalkingCospan (smallAffineEtaleToScheme S))

/- Lemma 34.4.10 (11): the final object of `(\mathit{Sch}/S)_{\acute{e}tale}` is `S/S`. -/
#check (Over.mkIdTerminal : IsTerminal (Over.mk (𝟙 S)))

/- Lemma 34.4.10 (12): the final object of `S_{\acute{e}tale}` is `S/S`. -/
#check
  (MorphismProperty.Over.mkIdTerminal (@Etale) S :
    IsTerminal
      (MorphismProperty.Over.mk ⊤ (𝟙 S) (inferInstance : Etale (𝟙 S)) : S.Etale))

end Scheme
end AlgebraicGeometry
