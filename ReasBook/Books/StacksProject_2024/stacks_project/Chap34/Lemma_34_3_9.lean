import Mathlib.CategoryTheory.Limits.Constructions.Over.Products
import StacksProject_2024.Chap34.Definition_34_3_7

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

noncomputable section

universe u

namespace AlgebraicGeometry
namespace Scheme

/- Semantic recall: the big Zariski site has underlying category `Scheme`; its slice-side and
small-site owners are the canonical `Over S` and `S.smallZariskiSite` from
`Definition_34_3_7`; and the affine variants already carry their pullback-preservation instances
there. Hence the source clauses here are direct recalls of the existing pullback-preservation and
terminal-object owners, rather than new wrapper declarations. -/

variable (S : Scheme.{u})

/- Lemma 34.3.9 (1): the ambient category of schemes has fibre products. -/
#check (inferInstance : HasPullbacks Scheme)

/- Lemma 34.3.9 (2): the obvious functor from the big Zariski site `Sch_{Zar}` to `Sch` commutes
with fibre products; in the canonical owner this is the identity functor on `Scheme`. -/
#check (inferInstance : PreservesLimitsOfShape WalkingCospan (𝟭 Scheme))

/- Lemma 34.3.9 (3): the underlying category of `(Sch/S)_{Zar}` has fibre products. -/
#check (inferInstance : HasPullbacks S.bigZariskiSite)

/- Lemma 34.3.9 (4): the obvious functor `(Sch/S)_{Zar} ⥤ Sch` commutes with fibre products. -/
#check (inferInstance : PreservesLimitsOfShape WalkingCospan (Over.forget S))

/- Lemma 34.3.9 (5): the underlying category of `S_{Zar}` has fibre products. -/
#check (inferInstance : HasPullbacks S.smallZariskiSite)

/- Lemma 34.3.9 (6): the obvious functor `S_{Zar} ⥤ Sch` commutes with fibre products. -/
#check
  (inferInstance :
    PreservesLimitsOfShape WalkingCospan (smallZariskiToScheme S))

/- Lemma 34.3.9 (7): the underlying category of `(Aff/S)_{Zar}` has fibre products. -/
#check (inferInstance : HasPullbacks S.bigAffineZariskiSite)

/- Lemma 34.3.9 (8): the obvious functor `(Aff/S)_{Zar} ⥤ Sch` commutes with fibre products. -/
#check
  (inferInstance :
    PreservesLimitsOfShape WalkingCospan
      (bigAffineZariskiToScheme S))

/- Lemma 34.3.9 (9): the underlying category of `S_{affine, Zar}` has fibre products. -/
#check (inferInstance : HasPullbacks S.smallAffineZariskiSite)

/- Lemma 34.3.9 (10): the obvious functor `S_{affine, Zar} ⥤ Sch` commutes with fibre
products. -/
#check
  (inferInstance :
    PreservesLimitsOfShape WalkingCospan
      (smallAffineZariskiToScheme S))

/- Lemma 34.3.9 (11): the category `(Sch/S)_{Zar}` has final object `S/S`. -/
#check (Over.mkIdTerminal : IsTerminal (Over.mk (𝟙 S)))

/- Lemma 34.3.9 (12): the category `S_{Zar}` has final object `S/S`. -/
#check
  (MorphismProperty.Over.mkIdTerminal IsOpenImmersion S :
    IsTerminal
      (MorphismProperty.Over.mk ⊤ (𝟙 S) (inferInstance : IsOpenImmersion (𝟙 S)) :
        S.smallZariskiSite))

end Scheme
end AlgebraicGeometry
