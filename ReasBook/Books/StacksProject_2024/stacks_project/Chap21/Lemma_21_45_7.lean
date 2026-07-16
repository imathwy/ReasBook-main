import StacksProject_2024.stacks_project.Chap21.Lemma_21_20_3
import StacksProject_2024.stacks_project.Chap21.Definition_21_45_1

open CategoryTheory
open CategoryTheory.Limits
open scoped RingedSiteCohomology

noncomputable section

universe u v

attribute [local instance] HasDerivedCategory.standard

set_option checkBinderAnnotations false

namespace RingedSite.Hom.ModuleDerived

section

/- Domain-style sampling for Lemma 21.45.7:
- primary domain: pseudo-coherent derived `𝒪_X`-modules on a ringed site and finiteness
  properties of their top surviving cohomology sheaves;
- sampled owner declarations:
  `RingedSite.Hom.ModuleDerived.IsMPseudoCoherent`,
  `DerivedCategory.IsLE`,
  `RingedSite.Hom.cohomologySheaf`,
  `RingedSite.Hom.ModuleCat`;
- best owner abstraction:
  `source-facing`: the two finiteness consequences of Lemma `21.45.7` for the cohomology sheaves
    `𝓗[m](X, K)` and `𝓗[(m + 1)](X, K)`;
  `core/canonical`: the Chapter 21 owner `K.IsMPseudoCoherent m` on `ModuleDerived X`, the
    canonical bounded-above owner `K.IsLE n`, and the cohomology-sheaf owner `𝓗[i](X, K)`;
  `bridge/view`: the vanishing reformulation encoded by `K.IsLE n`.

Primitive vs. derived:
- primitive data are the ringed site `X`, the derived object `K`, the integer `m`, the owner
  hypothesis `K.IsMPseudoCoherent m`, and the canonical bound `K.IsLE m` or `K.IsLE (m + 1)`;
- derived API is the finite-type and finite-presentation conclusions for the top cohomology
  sheaves.
-/

variable {X : RingedSite.{u, v}}

variable [HasBinaryProducts X.carrier]
variable [HasWeakSheafify X.siteTopology AddCommGrpCat.{max u v}]
variable [X.siteTopology.WEqualsLocallyBijective AddCommGrpCat.{max u v}]
variable [∀ U : X, (localizedRestriction X U).Additive]
variable [∀ U : X, PreservesFiniteLimits (localizedRestriction X U)]
variable [∀ U : X, PreservesFiniteColimits (localizedRestriction X U)]
variable [CategoryWithHomology (ModuleCat X)]
variable [∀ U : X, CategoryWithHomology (ModuleCat (X.localization U))]

local notation "DMod" => ModuleDerived X

variable {K : DMod} {m : ℤ}

/-- Lemma 21.45.7 (1): if `K ∈ D(𝒪_X)` is `m`-pseudo-coherent and belongs to `D^{≤ m}`, then
the cohomology sheaf `𝓗[m](X, K)` is a finite type `𝒪_X`-module. The `IsLE` hypothesis is the
canonical way to encode the vanishing `𝓗[i](X, K) = 0` for `i > m`. -/
@[stacks 08FX]
theorem IsMPseudoCoherent.topCohomology_isFiniteType
    (hK : K.IsMPseudoCoherent m)
    (hLE : K.IsLE m) :
    (𝓗[m](X, K)).IsFiniteType := by
  sorry

/-- Lemma 21.45.7 (2): if `K ∈ D(𝒪_X)` is `m`-pseudo-coherent and belongs to `D^{≤ m + 1}`,
then the cohomology sheaf `𝓗[(m + 1)](X, K)` is a finitely presented `𝒪_X`-module. The `IsLE`
hypothesis is the canonical way to encode the vanishing `𝓗[i](X, K) = 0` for `i > m + 1`. -/
@[stacks 08FX]
theorem IsMPseudoCoherent.nextCohomology_isFinitePresentation
    (hK : K.IsMPseudoCoherent m)
    (hLE : K.IsLE (m + 1)) :
    (𝓗[(m + 1)](X, K)).IsFinitePresentation := by
  sorry

end

end RingedSite.Hom.ModuleDerived
