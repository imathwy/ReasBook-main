import Mathlib
import StacksProject_2024.Chap13.Definition_13_37_1
import StacksProject_2024.Chap21.Lemma_21_52_3

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open CategoryTheory.Limits
open DerivedCategory
open Opposite

noncomputable section

universe u

attribute [local instance] HasDerivedCategory.standard

namespace SheafOfModules.RingedSite

section

variable {C : Type u} [Category.{u} C] {J : GrothendieckTopology C}
variable [J.HasSheafCompose (forget₂ CommRingCat RingCat)]
variable [HasWeakSheafify J AddCommGrpCat.{u}]
variable [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
variable [J.HasSheafCompose (forget₂ RingCat AddCommGrpCat.{u})]
variable {𝒪 : Sheaf J CommRingCat.{u}}

local notation "Mod" => SheafOfModules (ringSheaf J 𝒪)

/- Domain-style sampling for Lemma 21.52.5:
- primary domain: compactness of the standard generators `j_{U!}\mathcal O_U[0]` in the derived
  category of sheaves of modules on a ringed site;
- sampled owner declarations:
  `CategoryTheory.IsCompactObject`,
  `CategoryTheory.Sheaf.cohomologyPresheafFunctor`,
  `CategoryTheory.Sheaf.cohomologyPresheaf`,
  `SheafOfModules.toSheaf`,
  `SheafOfModules.RingedSite.localizedStructureModuleExtensionByZeroDegreeZero`;
- best owner abstraction: the source-facing owner is
  `localizedStructureModuleExtensionByZeroDegreeZero J 𝒪 U`, and the hypothesis layer is best
  expressed through the canonical underlying-abelian cohomology owners
  `F.cohomologyPresheaf p` and `Sheaf.cohomologyPresheafFunctor`;
- primitive data: the vanishing bound and direct-sum preservation for the ordinary site
  cohomology functors on `\mathcal O`-modules over the fixed object `U`;
- derived API: compactness of `j_{U!}\mathcal O_U[0]`.

Source/core/bridge triage:
- `source-facing`: the compactness statement for `j_{U!}\mathcal O_U[0]`;
- `core/canonical`: `CategoryTheory.IsCompactObject`;
- `bridge/view`: the canonical underlying-abelian cohomology presheaf
  `((SheafOfModules.toSheaf (ringSheaf J 𝒪)).obj ℱ).cohomologyPresheaf p` and its objectwise
  evaluation at `U`.
-/

-- Proof sketch: identify
-- `Hom_{D(\mathcal O)}(j_{U!}\mathcal O_U[0], K)` with `R\Gamma(U, K)`. The uniform bound on
-- `H^p(U, \mathcal F)` gives finite cohomological dimension for `\Gamma(U,-)`, and the
-- direct-sum hypothesis makes direct sums of injective resolutions acyclic for this functor. One
-- then computes `R\Gamma(U, \bigoplus_i K_i)` termwise on K-injective representatives and obtains
-- compatibility with arbitrary direct sums, which is exactly compactness of `j_{U!}\mathcal O_U`.
/-- Lemma 21.52.5: if there is an integer `d` such that `H^p(U, \mathcal F) = 0` for all
`p > d` and all sheaves `\mathcal F` of `\mathcal O`-modules, and if each functor
`\mathcal F \mapsto H^p(U, \mathcal F)` commutes with direct sums, then the degree-zero derived
object attached to `j_{U!}\mathcal O_U` is a compact object of `D(\mathcal O)`. -/
theorem localizedStructureModuleExtensionByZeroDegreeZero_isCompactObject_of_finiteCohomologicalDimension_and_directSumCompatibility
    (U : C)
    (hvanish :
      ∃ d : ℤ, ∀ (p : ℕ), d < p → ∀ ℱ : Mod,
        IsZero ((((SheafOfModules.toSheaf (ringSheaf J 𝒪)).obj ℱ).cohomologyPresheaf p).obj
          (op U)))
    (hcomm :
      ∀ (p : ℕ) (ι : Type u),
        PreservesColimitsOfShape (Discrete ι)
          (SheafOfModules.toSheaf (ringSheaf J 𝒪) ⋙
            Sheaf.cohomologyPresheafFunctor J p ⋙
              (CategoryTheory.evaluation Cᵒᵖ AddCommGrpCat.{u}).obj (op U))) :
    IsCompactObject (localizedStructureModuleExtensionByZeroDegreeZero J 𝒪 U) := sorry

end

end SheafOfModules.RingedSite
