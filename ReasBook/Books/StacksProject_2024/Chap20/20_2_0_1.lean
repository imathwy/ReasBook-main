import Mathlib
import StacksProject_2024.Chap20.«20_2_0_3»

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

universe u

open Opposite TopologicalSpace

namespace CategoryTheory
namespace Sheaf

variable {X : Type u} [TopologicalSpace X]
variable [HasSheafify (Opens.grothendieckTopology X) AddCommGrpCat.{u}]
variable [HasExt.{u} (Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u})]

/-- 20.2.0.1: the degree-`i` cohomology of a topological space `X` with coefficients in a sheaf
`F` is computed by the degree-`i` homology of the global-sections complex obtained from an
injective resolution `I^•` of `F`. -/
-- Proof sketch: specialize the standard injective-resolution computation of sheaf cohomology on a
-- site to the terminal object `⊤ : Opens X`, whose sections are the global sections on `X`.
theorem global_cohomology_isomorphic_to_homology_global_sections_of_injectiveResolution
    {F : Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}} (I : InjectiveResolution F)
    (i : ℕ) :
    IsIsomorphic (F.H' i (⊤ : Opens X))
      ((HomologicalComplex.homologyFunctor AddCommGrpCat (ComplexShape.up ℕ) i).obj
        ((((sheafSections (Opens.grothendieckTopology X) AddCommGrpCat).obj
          (op (⊤ : Opens X))).mapHomologicalComplex (ComplexShape.up ℕ)).obj I.cocomplex)) := by
  exact ⟨cohomologyAtObject_isomorphic_to_homology_sections_of_injectiveResolution
    (Opens.grothendieckTopology X) I i⟩

end Sheaf
end CategoryTheory
