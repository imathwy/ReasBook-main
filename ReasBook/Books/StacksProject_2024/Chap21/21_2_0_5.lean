import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

universe v u

open Opposite

namespace CategoryTheory
namespace Sheaf

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable [HasSheafify J AddCommGrpCat.{v}] [HasExt.{v} (Sheaf J AddCommGrpCat.{v})]

/-- 21.2.0.5: The cohomology of `U` with coefficients in `F` is canonically computed by
 the homology of the sections complex obtained from an injective resolution `I` of `F`. -/
-- Proof sketch: compare the Ext-based definition of `H^i(U, F)` with the standard computation
-- of cohomology by applying sections on `U` to a chosen injective resolution `I`.
theorem cohomologyOver_eq_homology_sections_of_injectiveResolution
    {F : Sheaf J AddCommGrpCat.{v}} (I : InjectiveResolution F) (i : ℕ) (U : C) :
    F.H' i U =
      (HomologicalComplex.homologyFunctor AddCommGrpCat.{v} (ComplexShape.up ℕ) i).obj
        ((((sheafSections J AddCommGrpCat.{v}).obj (op U)).mapHomologicalComplex
          (ComplexShape.up ℕ)).obj I.cocomplex) := sorry

end Sheaf
end CategoryTheory
