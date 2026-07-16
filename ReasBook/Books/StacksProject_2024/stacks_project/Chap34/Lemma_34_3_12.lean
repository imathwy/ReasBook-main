import Mathlib
import StacksProject_2024.stacks_project.Chap34.Definition_34_3_7

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open AlgebraicGeometry
open scoped TopCat

universe u v

namespace AlgebraicGeometry
namespace Scheme

-- Semantic recall: `lean_leansearch` surfaced the canonical affine-basis comparison
-- `Scheme.AffineZariskiSite.sheafEquiv`. For Lemma 34.3.12 the chapter-local owner
-- `S.smallZariskiTopology` from Definition 34.3.7 is the source-faithful full small Zariski site,
-- and the target owner is the usual set-valued sheaf category on the underlying topological space.

/-- Lemma 34.3.12: the category of sheaves of sets on `S_{Zar}` is equivalent to the category of
sheaves of sets on the underlying topological space of `S`. -/
def smallZariskiTypeSheafEquiv (S : Scheme.{u}) :
    Sheaf S.smallZariskiTopology (Type v) ≌
      TopCat.Sheaf (Type v) (S.toPresheafedSpace : TopCat) := sorry

/-- The unit comparison morphism for `smallZariskiTypeSheafEquiv` is an isomorphism on every
small Zariski sheaf. -/
theorem smallZariskiTypeSheafEquiv_unitIso_hom_app_isIso
    (S : Scheme.{u}) (ℱ : Sheaf S.smallZariskiTopology (Type v)) :
    IsIso ((smallZariskiTypeSheafEquiv S).unitIso.hom.app ℱ) :=
  sorry

end Scheme
end AlgebraicGeometry
