import StacksProject_2024.Chap21.Lemma_21_23_7

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open CategoryTheory.Limits
open RingedSite.Hom
open scoped RingedSiteCohomology

noncomputable section

universe u v

attribute [local instance] HasDerivedCategory.standard

/- Domain-style sampling for Lemma 21.23.9:
- primary domain: derived objectwise sections on a ringed site and truncation-limit comparison in
  `D(𝒪_X)`;
- sampled owner declarations:
  `RingedSite.Hom.ModuleCat`,
  `RingedSite.Hom.ModuleDerived`,
  `cohomologyOverObject`,
  `BasiswiseEventualCohomologySheafVanishing`,
  `CategoryTheory.IsTruncationDerivedLimitComparison`;
- best owner abstraction: the ambient module category and the objectwise cohomology owner already
  belong to the upstream Chapter 21 API around Lemma `21.23.7`, while the truncation-limit
  comparison owner is already provided by Remark `13.34.5`;
- primitive data: a ringed site `X`, a derived object `E`, a comparison map `c : E ⟶ K`, a basis
  candidate `B`, and the bound function `pBound`;
- derived API: this file is the source-facing uniform specialization of the eventual-vanishing
  owner from Lemma `21.23.7`, proved by the upstream bridge
  `BasiswiseEventualCohomologySheafVanishing.of_uniform`.

Source/core/bridge triage:
- `source-facing`: the isomorphism criterion for a compatible map
  from `E` to a derived inverse limit of its truncation tower;
- `core/canonical`: `ModuleCat`, `ModuleDerived`, `cohomologyOverObject`,
  `BasiswiseEventualCohomologySheafVanishing`, and `IsTruncationDerivedLimitComparison`;
- `bridge/view`: none in this file. -/

section

variable (X : RingedSite.{u, v})

variable [CategoryWithHomology (ModuleCat X)]
variable [IsGrothendieckAbelian.{max u v} (ModuleCat X)]
variable [HasWeakSheafify X.siteTopology AddCommGrpCat.{max u v}]

local notation "ModX" => ModuleCat X
local notation "DModX" => ModuleDerived X
local notation "single0" => DerivedCategory.singleFunctor ModX (0 : ℤ)

-- Proof sketch: this is the uniform-basis specialization of Lemma `21.23.7`. For each basis
-- object `V ∈ B`, use the constant bound family `pBound(V, m) := pBound m` and let `Cov_V` be
-- the coverings of `V` whose members all lie in `B`; the covering hypothesis makes this family
-- cofinal, so Lemma `21.23.7` applies to the cohomology sheaves `H^{m-p}(E)` and yields that any
-- compatible truncation-derived-limit comparison `c : E ⟶ K` is an isomorphism.
/-- Lemma 21.23.9: let `(𝒞, 𝒪)` be a ringed site, let `E ∈ D(𝒪)`,
and assume there are a function `pBound : ℤ → ℤ` and a subset `B` of objects of
`𝒞` such that every object admits a covering by members of `B` and
`H^p(V, H^{m-p}(E)) = 0` for every `V ∈ B` whenever `p > pBound(m)`. Then any compatible map
from `E` to a chosen derived inverse limit of its truncation tower, formalizing the canonical map
from Remark `13.34.5`, is an isomorphism in `D(𝒪)`. -/
@[stacks 08U3]
theorem truncationComparison_isIso_of_uniform_basiswise_eventual_cohomologySheaf_vanishing
    (E K : DModX)
    (c : E ⟶ K)
    (hc : IsTruncationDerivedLimitComparison E K c)
    (pBound : ℤ → ℤ)
    (B : Set X)
    (hcover : X.siteTopology.HasEnoughObjectsWithProperty (· ∈ B))
    (hvanish :
      ∀ ⦃V : X⦄, V ∈ B → ∀ p m : ℤ, pBound m < p →
        IsZero
          (H^p(V,
            (single0).obj (𝓗[(m - p)](X, E))))) :
    IsIso c := by
  exact
    truncationComparison_isIso_of_basiswise_eventual_cohomologySheaf_vanishing
      X E K c hc B hcover
      (fun V _ ↦
        BasiswiseEventualCohomologySheafVanishing.of_uniform X pBound B hcover hvanish V)

end
