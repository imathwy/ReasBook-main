import StacksProject_2024.stacks_project.Chap21.Lemma_21_23_7

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open CategoryTheory.Limits
open RingedSite.Hom
open scoped RingedSiteCohomology

noncomputable section

universe u v

attribute [local instance] HasDerivedCategory.standard

/-
Domain-style sampling for Lemma 21.23.8:
- primary domain: truncation-derived-limit comparisons in `D(𝒪_X)` on a ringed site and
  basiswise vanishing of higher cohomology for the negative cohomology sheaves;
- sampled owner declarations:
  `RingedSite.Hom.ModuleCat`,
  `RingedSite.Hom.ModuleDerived`,
  `cohomologyOverObject`,
  `BasiswiseEventualCohomologySheafVanishing`,
  `CategoryTheory.IsTruncationDerivedLimitComparison`;
- best owner abstraction: this file is source-facing for the stronger negative-degree hypothesis,
  while the eventual-vanishing owner already belongs to `Lemma_21_23_7`; this file should only
  keep the negative-degree owner and the canonical bridge to that upstream owner;
- primitive data: a basis object `V`, a degree bound `dV`, and a cofinal family `CovV`;
- derived API: the bridge
  `BasiswiseNegativeCohomologySheafVanishing.toEventual`.

Source/core/bridge triage:
- `source-facing`: the negative-degree hypothesis in the theorem statement below;
- `core/canonical`: `ModuleCat X`, `ModuleDerived X`,
  `cohomologyOverObject`, `BasiswiseEventualCohomologySheafVanishing`, and
  `IsTruncationDerivedLimitComparison`;
- `bridge/view`: `BasiswiseNegativeCohomologySheafVanishing.toEventual`. -/

section

variable (X : RingedSite.{u, v})

local notation "ModX" => ModuleCat X
local notation "DModX" => ModuleDerived X
local notation "single0" => DerivedCategory.singleFunctor ModX (0 : ℤ)

variable [CategoryWithHomology (ModuleCat X)]
variable [IsGrothendieckAbelian.{max u v} (ModuleCat X)]
variable [HasWeakSheafify X.siteTopology AddCommGrpCat.{max u v}]

/-- Negative-degree local vanishing over a fixed basis object `V`, expressed using some cofinal
covering system of `V`. -/
def BasiswiseNegativeCohomologySheafVanishing
    (E : DModX) (V : X) : Prop :=
  ∃ dV : ℕ, ∃ CovV : X.siteTopology.Cover V → Prop,
    (∀ S : X.siteTopology.Cover V,
      ∃ T : X.siteTopology.Cover V, CovV T ∧ Nonempty (T ⟶ S)) ∧
    ∀ ⦃T : X.siteTopology.Cover V⦄, CovV T → ∀ I : T.Arrow, ∀ p q : ℤ,
      (dV : ℤ) < p → q < 0 →
        IsZero (H^p(I.Y, (single0).obj (𝓗[q](X, E))))

-- Proof sketch: use the bound function `pBound(V, m) = d_V + max 0 m`. If
-- `p > d_V + max 0 m`, then `m - p < 0` and the assumed negative-degree vanishing applies.
omit [CategoryWithHomology (ModuleCat X)]
  [IsGrothendieckAbelian.{max u v} (ModuleCat X)]
  [HasWeakSheafify X.siteTopology AddCommGrpCat.{max u v}] in
/-- The negative-degree vanishing hypothesis from Lemma `21.23.8` implies the eventual
cohomology-sheaf vanishing owner from Lemma `21.23.7`. -/
theorem BasiswiseNegativeCohomologySheafVanishing.toEventual
    {E : DModX} {V : X}
    (h : BasiswiseNegativeCohomologySheafVanishing X E V) :
    BasiswiseEventualCohomologySheafVanishing X E V := by
  rcases h with ⟨dV, CovV, hcofinal, hneg⟩
  refine ⟨fun m ↦ (dV : ℤ) + max 0 m, CovV, hcofinal, ?_⟩
  intro T hT I p m hp
  rcases lt_or_ge m 0 with hm | hm
  · have hd : (dV : ℤ) < p := by
      simpa [max_eq_left_of_lt hm] using hp
    have hq : m - p < 0 := by
      omega
    exact hneg hT I p (m - p) hd hq
  · have hdp : (dV : ℤ) + m < p := by
      simpa [max_eq_right hm] using hp
    have hd : (dV : ℤ) < p := by
      omega
    have hq : m - p < 0 := by
      omega
    exact hneg hT I p (m - p) hd hq

-- Proof sketch: apply the eventual-vanishing truncation criterion with the bound function
-- `pBound(V, m) = d_V + max 0 m`, produced by the previous bridge.
/-- Lemma 21.23.8: let `(𝒞, 𝒪)` be a ringed site, let `E : D(𝒪)`, and let `B` be a subset of
objects of `𝒞`. Assume every object has a covering by members of `B`, and for each `V ∈ B` there
exist a nonnegative integer `d_V` and a cofinal system `CovV` of coverings of `V` such that
`H^p(V_i, H^q(E)) = 0` for every member `V_i` of every covering in `CovV` whenever `p > d_V` and
`q < 0`. Then every compatible comparison map from `E` to a chosen derived inverse limit of its
truncation tower is an isomorphism in `D(𝒪)`. -/
@[stacks 0D6N]
theorem truncationComparison_isIso_of_basiswise_negative_cohomologySheaf_vanishing
    (E K : DModX)
    (c : E ⟶ K)
    (hc : IsTruncationDerivedLimitComparison E K c)
    (B : Set X)
    (hcover : X.siteTopology.HasEnoughObjectsWithProperty (· ∈ B))
    (hvanish :
      ∀ ⦃V : X⦄, V ∈ B →
        BasiswiseNegativeCohomologySheafVanishing X E V) :
    IsIso c := by
  refine truncationComparison_isIso_of_basiswise_eventual_cohomologySheaf_vanishing
    X E K c hc B hcover ?_
  intro V hV
  simpa using
    (BasiswiseNegativeCohomologySheafVanishing.toEventual X (hvanish hV))

end
