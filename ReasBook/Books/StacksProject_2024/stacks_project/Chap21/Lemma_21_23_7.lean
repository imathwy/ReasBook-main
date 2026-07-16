import StacksProject_2024.stacks_project.Chap13.Remark_13_34_5
import StacksProject_2024.stacks_project.Chap07.Definition_7_40_2
import StacksProject_2024.stacks_project.Chap21.Lemma_21_20_3

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open CategoryTheory.Limits
open RingedSite.Hom
open scoped RingedSiteCohomology

noncomputable section

universe u v

attribute [local instance] HasDerivedCategory.standard

/-
Domain-style sampling for Lemma 21.23.7:
- primary domain: truncation-derived-limit comparisons in `D(𝒪_X)` on a ringed site,
  together with basiswise eventual vanishing for the cohomology sheaves of a derived object;
- sampled owner declarations:
  `ModuleCat`,
  `ModuleDerived`,
  `cohomologyOverObject`,
  `CategoryTheory.IsTruncationDerivedLimitComparison`,
  `CategoryTheory.GrothendieckTopology.HasEnoughObjectsWithProperty`;
- best owner abstraction: the truncation-limit comparison is already owned by the Chapter 13
  declaration `IsTruncationDerivedLimitComparison`, while the ambient module and derived
  categories are already owned upstream by `ModuleCat X` and `ModuleDerived X`; the canonical
  site-theoretic cover hypothesis is already owned by
  `X.siteTopology.HasEnoughObjectsWithProperty (· ∈ B)` from Definition `7.40.2`; the
  source-facing content here is only the local eventual-vanishing hypothesis on basis objects;
- primitive data: an object `V`, a bound function `pBound`, and a cofinal family `CovV` of
  coverings of `V`;
- derived API: the source-facing existence predicate
  `BasiswiseEventualCohomologySheafVanishing` and its uniform-basis specialization bridge below.

Source/core/bridge triage:
- `source-facing`: `BasiswiseEventualCohomologySheafVanishing`;
- `core/canonical`: `ModuleCat X`, `ModuleDerived X`,
  `cohomologyOverObject`, and
  `IsTruncationDerivedLimitComparison`, and
  `X.siteTopology.HasEnoughObjectsWithProperty (· ∈ B)`;
- `bridge/view`: `BasiswiseEventualCohomologySheafVanishing.of_uniform`; the
  negative-degree specialization lives in `Lemma_21_23_8`. -/

section

variable (X : RingedSite.{u, v})

variable [CategoryWithHomology (ModuleCat X)]
variable [IsGrothendieckAbelian.{max u v} (ModuleCat X)]
variable [HasWeakSheafify X.siteTopology AddCommGrpCat.{max u v}]

local notation "ModX" => ModuleCat X
local notation "DModX" => ModuleDerived X
local notation "single0" => DerivedCategory.singleFunctor ModX (0 : ℤ)

/-- Eventual local vanishing for the cohomology sheaves of a derived object over a fixed object
`V`, expressed using some cofinal covering system of `V`. -/
def BasiswiseEventualCohomologySheafVanishing
    (E : DModX) (V : X) : Prop :=
  ∃ pBound : ℤ → ℤ, ∃ CovV : X.siteTopology.Cover V → Prop,
    (∀ S : X.siteTopology.Cover V,
      ∃ T : X.siteTopology.Cover V, CovV T ∧ Nonempty (T ⟶ S)) ∧
    ∀ ⦃T : X.siteTopology.Cover V⦄, CovV T → ∀ I : T.Arrow, ∀ p m : ℤ,
      pBound m < p →
        IsZero
          (H^p(I.Y,
            (single0).obj (𝓗[(m - p)](X, E))))

-- Proof sketch: take `CovV` to be the coverings of `V` whose members all lie in `B`; the global
-- covering hypothesis makes this family cofinal over `V`, and the uniform vanishing hypothesis
-- gives the required vanishing on each member of such a cover.
/- A uniform basiswise vanishing hypothesis yields the source-facing owner
`BasiswiseEventualCohomologySheafVanishing` over every object by restricting to basis covers. -/
theorem BasiswiseEventualCohomologySheafVanishing.of_uniform
    {E : DModX}
    (pBound : ℤ → ℤ)
    (B : Set X)
    (hcover : X.siteTopology.HasEnoughObjectsWithProperty (· ∈ B))
    (hvanish :
      ∀ ⦃V : X⦄, V ∈ B → ∀ p m : ℤ, pBound m < p →
        IsZero
          (H^p(V,
            (single0).obj (𝓗[(m - p)](X, E)))))
    (V : X) :
    BasiswiseEventualCohomologySheafVanishing X E V := by
  sorry

-- Proof sketch: for each `V ∈ B`, apply the stated vanishing bounds on the cover system `CovV`
-- to the cohomology sheaves `H^{m-p}(E)`, use the truncation triangles from Remark `13.12.4` to
-- obtain eventual isomorphisms on the towers `H^{m-1}(V_i, τ_{\ge -n} E)` and
-- `H^m(V_i, τ_{\ge -n} E)`, deduce eventual injectivity from Lemma `21.23.6`, and then apply
-- the comparison-independence criterion of Remark `13.34.5`.
/- Lemma 21.23.7: let `(𝒞, 𝒪)` be a ringed site, let `E ∈ D(𝒪)`, and let `B` be a subset of
objects of `𝒞`. Assume every object of `𝒞` has a covering by members of `B`, and for each
`V ∈ B` there are a bound `pBound(V, -) : ℤ → ℤ` and a cofinal system `CovV` of coverings of
`V` such that `H^p(V_i, H^{m - p}(E)) = 0` for every member `V_i` of every covering in `CovV`
whenever `p > pBound(V, m)`. Then any compatible map from `E` to a chosen derived inverse limit
of the truncation tower is an isomorphism in `D(𝒪)`. -/
@[stacks 0D6M]
theorem truncationComparison_isIso_of_basiswise_eventual_cohomologySheaf_vanishing
    (E K : DModX)
    (c : E ⟶ K)
    (hc : IsTruncationDerivedLimitComparison E K c)
    (B : Set X)
    (hcover : X.siteTopology.HasEnoughObjectsWithProperty (· ∈ B))
    (hvanish :
      ∀ ⦃V : X⦄, V ∈ B →
        BasiswiseEventualCohomologySheafVanishing X E V) :
    IsIso c := by
  sorry

end
