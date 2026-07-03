import Mathlib

open CategoryTheory Opposite Limits

universe v u

namespace CategoryTheory
namespace Sheaf

/-- 20.2.0.3: for an injective resolution `I^•` of an abelian sheaf `\mathcal F`, the sheaf
cohomology `H^i(X, \mathcal F)` is canonically isomorphic to the `i`-th homology of the sections
complex `Γ(X, I^•)`. -/
-- Proof sketch: apply the canonical right-derived comparison on the sections functor `Γ(X, -)`
-- to the chosen injective resolution `I`.
theorem cohomologyAtObject_isomorphic_to_homology_sections_of_injectiveResolution
    {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
    [HasSheafify J AddCommGrpCat.{v}]
    [HasExt.{v} (Sheaf J AddCommGrpCat.{v})]
    {X : C} {F : Sheaf J AddCommGrpCat.{v}} (I : InjectiveResolution F) (i : ℕ) :
    IsIsomorphic (F.H' i X)
      ((HomologicalComplex.homologyFunctor AddCommGrpCat (ComplexShape.up ℕ) i).obj
        ((((sheafSections J AddCommGrpCat.{v}).obj (op X)).mapHomologicalComplex
          (ComplexShape.up ℕ)).obj I.cocomplex)) := sorry

end Sheaf
end CategoryTheory
