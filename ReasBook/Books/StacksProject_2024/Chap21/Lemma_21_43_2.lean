import Mathlib
import Mathlib.Algebra.Homology.DerivedCategory.Basic
import Mathlib.Algebra.Homology.DerivedCategory.TStructure
import Mathlib.CategoryTheory.ObjectProperty.ColimitsOfShape
import Mathlib.CategoryTheory.ObjectProperty.Extensions
import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory
import Mathlib.CategoryTheory.ObjectProperty.Kernels
import Mathlib.CategoryTheory.ObjectProperty.Retract
import Mathlib.CategoryTheory.Triangulated.Subcategory
import StacksProject_2024.Chap13.Lemma_13_17_1
import StacksProject_2024.Chap18.Lemma_18_24_4
import StacksProject_2024.Chap18.Definition_18_34_1

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.ObjectProperty
open Opposite

noncomputable section

universe w u v

attribute [local instance] HasDerivedCategory.standard

namespace CategoryTheory

/- Domain-style sampling for Lemma 21.43.2:
- primary domain: weak-LinearRepresentations_Serre_1977 object properties on abelian categories and the derived subcategories
  they cut out by cohomology conditions;
- sampled owner declarations:
  `derivedCategoryCohomologyInProperty`,
  `DerivedCategoryWithCohomologyIn`,
  `derivedCategoryCohomologyInProperty_isClosedUnderIsomorphisms`,
  `derivedCategoryCohomologyInProperty_isTriangulated`;
- best owner abstraction: the Chapter 13 owner
  `derivedCategoryCohomologyInProperty P` on `DerivedCategory A`, with the corresponding full
  subcategory owner `DerivedCategoryWithCohomologyIn P`;
- primitive data: an ambient object property `P : ObjectProperty A`;
- derived API: strict fullness, saturation, triangulated closure, and the colimit-closure result
  for the owner property on `D(A)`.

Source/core/bridge triage:
- `source-facing`: the chaotic-site quasi-coherent derived subcategory `QC(\mathcal O)`;
- `core/canonical`: `derivedCategoryCohomologyInProperty` and
  `DerivedCategoryWithCohomologyIn`;
- `bridge/view`: the specialization to the quasi-coherent module property on
  `Mod(\mathcal O)`. -/

end CategoryTheory

namespace SheafOfModules.ChaoticSite

variable {C : Type u} [Category.{v} C]
variable (𝒪 : Sheaf (⊥ : GrothendieckTopology C) CommRingCat)
variable [((⊥ : GrothendieckTopology C)).HasSheafCompose (forget₂ CommRingCat RingCat)]
variable [∀ U : C, ((⊥ : GrothendieckTopology C).over U).HasSheafCompose
  (forget₂ RingCat AddCommGrpCat)]
variable [∀ U : C, HasWeakSheafify ((⊥ : GrothendieckTopology C).over U) AddCommGrpCat]
variable [∀ U : C, ((⊥ : GrothendieckTopology C).over U).WEqualsLocallyBijective AddCommGrpCat]

local notation "Mod𝒪" => chaoticModuleCategory 𝒪
local notation "QCoh" =>
  SheafOfModules.isQuasicoherent (ringSheaf (⊥ : GrothendieckTopology C) 𝒪)
local notation "DQCoh" => derivedCategoryCohomologyInProperty QCoh

variable [Abelian Mod𝒪]
variable [Fact (∀ ⦃U V : C⦄ (f : U ⟶ V), RingHom.Flat ((𝒪.obj.map f.op).hom))]

-- Proof sketch: flat restriction maps make quasi-coherent modules on the chaotic site into a weak
-- LinearRepresentations_Serre_1977 subcategory by Lemma `18.24.4`; then the generic derived-category statement for
-- `D_P(A)` shows that the degreewise quasi-coherent condition is preserved under isomorphisms.
/-- The object property defining `QC(\mathcal O)` is strictly full inside `D(\mathcal O)`. -/
instance derivedQuasiCoherentProperty_isClosedUnderIsomorphisms :
    ObjectProperty.IsClosedUnderIsomorphisms DQCoh :=
  derivedCategoryCohomologyInProperty_isClosedUnderIsomorphisms QCoh

-- Proof sketch: after Lemma `18.24.4`, quasi-coherent modules form a weak LinearRepresentations_Serre_1977 subcategory of
-- `Mod(\mathcal O)`, and the generic saturation result for `D_P(A)` identifies retracts in the
-- derived category with direct summands of all cohomology modules.
/-- The object property defining `QC(\mathcal O)` is saturated, i.e. stable under retracts in
`D(\mathcal O)`. -/
instance derivedQuasiCoherentProperty_isStableUnderRetracts :
    ObjectProperty.IsStableUnderRetracts DQCoh :=
  derivedCategoryCohomologyInProperty_isSaturated QCoh

-- Proof sketch: flat restriction maps on the chaotic site imply that quasi-coherent
-- `\mathcal O`-modules form a weak LinearRepresentations_Serre_1977 subcategory of `Mod(\mathcal O)`. The derived
-- cohomology-in-subcategory criterion then shows that the degreewise quasi-coherent condition is
-- preserved under zero objects, shifts, and distinguished triangles.
/-- Lemma 21.43.2: in the chaotic-site module situation, the object property cutting out
`QC(\mathcal O) \subset D(\mathcal O)` is triangulated. The companion declarations in this file
record the strict fullness, saturation, and arbitrary direct-sum closure asserted in the same
lemma. -/
instance derivedQuasiCoherentProperty_isTriangulated :
    ObjectProperty.IsTriangulated DQCoh :=
  derivedCategoryCohomologyInProperty_isTriangulated QCoh

-- Proof sketch: apply the previous colimit-closure criterion to the object property of
-- quasi-coherent `\mathcal O`-modules, using that `H^n` commutes with the chosen coproducts and
-- that quasi-coherent modules are already closed under those coproducts.
/-- If quasi-coherent `\mathcal O`-modules are closed under `ι`-indexed direct sums and each
cohomology functor on `D(\mathcal O)` commutes with those sums, then `QC(\mathcal O)` is also
closed under `ι`-indexed direct sums. -/
instance derivedQuasiCoherentProperty_isClosedUnderDirectSums
    (ι : Type w)
    [IsClosedUnderColimitsOfShape
      QCoh
      (Discrete ι)]
    [∀ n : ℤ, PreservesColimitsOfShape (Discrete ι)
      (DerivedCategory.homologyFunctor Mod𝒪 n)] :
    ObjectProperty.IsClosedUnderColimitsOfShape DQCoh (Discrete ι) :=
  derivedCategoryCohomologyInProperty_isClosedUnderColimitsOfShape QCoh (Discrete ι)

end SheafOfModules.ChaoticSite
