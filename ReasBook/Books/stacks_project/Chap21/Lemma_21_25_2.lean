import Mathlib
import stacks_project.Chap13.Lemma_13_17_1
import stacks_project.Chap13.Remark_13_34_5
import stacks_project.Chap18.Definition_18_6_1
import stacks_project.Chap21.Situation_21_25_1

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open CategoryTheory.GrothendieckTopology

noncomputable section

universe u v

attribute [local instance] HasDerivedCategory.standard

section

/-- The abelian category `\mathrm{Mod}(\mathcal O_X)` of sheaves of modules on the ringed site
`X`. -/
private abbrev RingedSiteModuleCat (X : RingedSite.{u, v}) :=
  SheafOfModules X.structureSheaf

variable (X : RingedSite.{u, v})

local notation "ModX" => RingedSiteModuleCat X

variable [HasWeakSheafify X.siteTopology AddCommGrpCat]
variable [HasSheafify X.siteTopology AddCommGrpCat]
variable [HasExt (Sheaf X.siteTopology AddCommGrpCat)]
variable [X.siteTopology.WEqualsLocallyBijective AddCommGrpCat]
variable [Abelian ModX]

variable (A : ObjectProperty ModX)
variable [A.ContainsZero] [A.IsClosedUnderKernels] [A.IsClosedUnderCokernels]
variable [A.IsClosedUnderExtensions]

-- Proof sketch: an object of `D_\mathcal A(\mathcal O_X)` has all cohomology sheaves in `A`.
-- Apply Lemma `21.23.8` to the bounded-cohomology basis from Situation `21.25.1`, using its
-- vanishing hypothesis for the negative cohomology sheaves of `E.obj`; Remark `13.34.5`
-- identifies the compatible comparison morphism with the textbook map
-- `E \to R\!\varprojlim_n \tau_{\ge -n} E`.
/-- Lemma 21.25.2: in Situation `21.25.1`, if `E` is a derived `\mathcal O_X`-module whose
cohomology sheaves all lie in the weak Serre subcategory `\mathcal A`, then any compatible
morphism formalizing the canonical map
`E \to R\!\varprojlim_n \tau_{\ge -n} E` is an isomorphism in `D(\mathcal O_X)`. -/
theorem truncationComparison_isIso_of_mem_derivedCategoryWithCohomologyIn
    (basis : bounded_cohomology_basis X.structureSheaf A)
    (E : DerivedCategoryWithCohomologyIn A)
    (K : DerivedCategory ModX)
    (c : E.obj ⟶ K)
    (hc : IsTruncationDerivedLimitComparison E.obj K c) :
    IsIso c := sorry

end
