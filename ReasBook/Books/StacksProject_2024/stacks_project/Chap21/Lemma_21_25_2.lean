import StacksProject_2024.Chap13.Aux_13_17_1
import StacksProject_2024.Chap13.Remark_13_34_5
import StacksProject_2024.Chap21.Lemma_21_19_1_core
import StacksProject_2024.Chap21.Situation_21_25_1

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open CategoryTheory.GrothendieckTopology
open scoped DerivedCategoryWithCohomologyIn

noncomputable section

universe u v

attribute [local instance] HasDerivedCategory.standard

namespace RingedSite.Hom

section

variable (X : RingedSite.{u, v})

local notation "ModX" => ModuleCat X

variable [HasSheafify X.siteTopology AddCommGrpCat]
variable [HasExt (Sheaf X.siteTopology AddCommGrpCat)]
variable [Abelian ModX]

variable (A : ObjectProperty ModX)

/- Domain-style sampling for Lemma 21.25.2:
- primary domain: truncation-derived-limit comparisons in `D(𝒪_X)` on a ringed site,
  specialized to the full subcategory cut out by the Chapter 13 owner
  `DerivedCategoryWithCohomologyIn A` and to the bounded-cohomology-basis data of Situation
  `21.25.1`;
- sampled owner declarations:
  `DerivedCategoryWithCohomologyIn A`,
  `ModuleCat X`,
  `ModuleDerived X`,
  `CategoryTheory.DerivedCategoryWithCohomologyIn`,
  `CategoryTheory.IsTruncationDerivedLimitComparison`,
  `truncationComparison_isIso_of_basiswise_negative_cohomologySheaf_vanishing`;
- best owner abstraction: this file is only a `bridge/view` statement. The ambient module and
  derived categories should be expressed by the chapter owners for the module category on a
  ringed site and its derived category, while the cohomology-membership hypothesis should reuse
  the Chapter 13 owner `DerivedCategoryWithCohomologyIn A`, and the comparison condition should
  stay on the canonical owner `IsTruncationDerivedLimitComparison`;
- primitive data: the ringed site `X`, the object property `A`, the bounded-cohomology basis from
  Situation `21.25.1`, the object `E : D_{A}`, the comparison target `K`, and the compatible map
  `c : E.obj ⟶ K`;
- derived API: no new owner is introduced here; the theorem below is the source-facing bridge from
  the bounded-cohomology-basis hypotheses to the canonical truncation-comparison predicate.

Source/core/bridge triage:
- `source-facing`: the Stacks-project bridge criterion for objects of `D_{A}(𝒪_X)`;
- `core/canonical`: `ModuleDerived X`, `D_{A}`,
  `IsTruncationDerivedLimitComparison`, and the Chapter 21 truncation-comparison theorem;
- `bridge/view`: the theorem
  `truncationComparison_isIso_of_mem_derivedCategoryWithCohomologyIn` itself. -/

-- Proof sketch: an object of `D_{A}(𝒪_X)` has all cohomology sheaves in `A`.
-- Apply Lemma `21.23.8` to the bounded-cohomology basis from Situation `21.25.1`, using its
-- vanishing hypothesis for the negative cohomology sheaves of `E.obj`; Remark `13.34.5`
-- identifies the compatible comparison morphism with the textbook map
-- `E ⟶ R lim_n τ_{≥ -n} E`.
/-- Lemma 21.25.2: in Situation `21.25.1`, if `E` is a derived `𝒪_X`-module whose cohomology
sheaves all lie in the weak Serre subcategory `𝒜`, then any compatible morphism formalizing the
canonical map `E ⟶ R lim_n τ_{≥ -n} E` is an isomorphism in `D(𝒪_X)`. -/
@[stacks 0D6S]
theorem truncationComparison_isIso_of_mem_derivedCategoryWithCohomologyIn
    (basis : BoundedCohomologyBasis X.structureSheaf A)
    (E : D_{A})
    (K : ModuleDerived X)
    (c : E.obj ⟶ K)
    (hc : IsTruncationDerivedLimitComparison E.obj K c) :
    IsIso c := sorry

end

end RingedSite.Hom
