import Mathlib

open CategoryTheory

universe v u

namespace CategoryTheory
namespace Sheaf

/- Domain-style sampling for 21.2.0.6:
- primary domain: sheaf cohomology on a site, computed from a chosen injective resolution by
  applying the global-sections functor;
- sampled owner API:
  `CategoryTheory.Sheaf.H`,
  `CategoryTheory.Sheaf.Γ`,
  `CategoryTheory.HasGlobalSectionsFunctor`,
  `CategoryTheory.InjectiveResolution`,
  `CategoryTheory.InjectiveResolution.isoRightDerivedObj`;
- best owner abstraction: the cohomology object `F.H i`, with the global-sections owner
  `Sheaf.Γ J AddCommGrpCat` providing the source-facing resolution model;
- primitive data: a site `(C, J)`, a sheaf `F`, an injective resolution `I : InjectiveResolution F`,
  and a degree `i : ℕ`;
- derived API: the degree-`i` homology of the global-sections complex
  `(((Sheaf.Γ J AddCommGrpCat).mapHomologicalComplex (ComplexShape.up ℕ)).obj I.cocomplex)`.

Source/core/bridge triage:
- `source-facing`: the formula `H^i(\mathcal C, \mathcal F) = H^i(\Gamma(\mathcal C, I^\bullet))`;
- `core/canonical`: `CategoryTheory.Sheaf.H` and `CategoryTheory.Sheaf.Γ`;
- `bridge/view`: the comparison isomorphism from `F.H i` to the homology of the global-sections
  complex of a chosen injective resolution.

There is no exact upstream owner declaration in the project with this interface, so the refined
file keeps only this thin bridge theorem and does not introduce any extra wrapper names. -/

/-- 21.2.0.6: for an abelian sheaf `F` on a site `(C, J)`, a chosen injective resolution
`F ⟶ I^•`, and `i : ℕ`, the global sheaf cohomology `H^i(\mathcal C, F)` is canonically
isomorphic to the degree-`i` homology of the global-sections complex `Γ(\mathcal C, I^•)`. -/
theorem cohomology_isomorphic_to_homology_global_sections_of_injectiveResolution
    {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
    [HasGlobalSectionsFunctor J AddCommGrpCat.{v}]
    [HasSheafify J AddCommGrpCat.{v}]
    [HasExt.{v} (Sheaf J AddCommGrpCat.{v})]
    {F : Sheaf J AddCommGrpCat.{v}} (I : InjectiveResolution F) (i : ℕ) :
    IsIsomorphic (AddCommGrpCat.of (F.H i))
      ((HomologicalComplex.homologyFunctor AddCommGrpCat.{v} (ComplexShape.up ℕ) i).obj
        (((Sheaf.Γ J AddCommGrpCat.{v}).mapHomologicalComplex (ComplexShape.up ℕ)).obj
          I.cocomplex)) := sorry

end Sheaf
end CategoryTheory
