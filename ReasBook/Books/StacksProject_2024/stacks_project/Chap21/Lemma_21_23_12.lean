import StacksProject_2024.Chap07.Definition_7_40_2
import StacksProject_2024.Chap13.Definition_13_34_1
import StacksProject_2024.Chap21.Lemma_21_23_5
import StacksProject_2024.Chap21.Lemma_21_20_7_core

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.SequentialInverseSystem
open RingedSite.Hom
open scoped RingedSiteCohomology

noncomputable section

universe u v

attribute [local instance] HasDerivedCategory.standard

/- Domain-style sampling for Lemma 21.23.12:
- primary domain: sequential derived inverse limits of `𝒪_X`-modules on a ringed site,
  together with their cohomology sheaves and objectwise sections over a basis;
- sampled owner declarations:
  `CategoryTheory.GrothendieckTopology.HasEnoughObjectsWithProperty`,
  `RingedSite.Hom.moduleSectionsAsAbelianFunctor`,
  `RingedSite.Hom.cohomologySheaf`,
  `RingedSite.Hom.cohomologyOverObject`,
  `CategoryTheory.SequentialInverseSystem.firstDerivedLimit`,
  `BasiswiseSingleAcyclic`,
  `BasiswiseFirstDerivedLimitIsZero`;
- best owner abstraction: this file is `source-facing`, but Chapter 21 already owns the
  site-cover hypothesis by `X.siteTopology.HasEnoughObjectsWithProperty (· ∈ B)`,
  the cohomology-sheaf/objectwise-cohomology owners by `𝓗[q](X, -)` and `H^q(U, -)`, and the
  sections functor by `moduleSectionsAsAbelianFunctor`; the Milnor
  `R^1 lim` term is canonically the `firstDerivedLimit` of the sections tower
  `Ksys ⋙ HMod q ⋙ moduleSectionsAsAbelianFunctor X U`, while the basiswise acyclicity and
  basiswise `R^1 lim` hypotheses are already canonically owned in Chapter 21 by
  `BasiswiseSingleAcyclic` and `BasiswiseFirstDerivedLimitIsZero` applied to the module tower
  `Ksys ⋙ HMod q`;
- primitive data: a ringed site `X`, a sequential inverse system
  `Ksys : ℕᵒᵖ ⥤ ModuleDerived X`, a chosen derived limit `K`, a covering subset `B`, and a
  cohomological degree `q`;
- derived API: the canonical cohomology-sheaf tower `Ksys ⋙ HMod q`, the reused basiswise
  hypothesis owners from Lemma `21.23.5`, and the source-facing limit comparison theorem below.

Source/core/bridge triage:
- `source-facing`: the cohomology-sheaf comparison theorem below;
- `core/canonical`: `ModuleCat`, `ModuleDerived`,
  `X.siteTopology.HasEnoughObjectsWithProperty (· ∈ B)`,
  `cohomologySheaf`, `cohomologyOverObject`,
  `moduleSectionsAsAbelianFunctor`, `DerivedCategory.homologyFunctor`, and
  `SequentialInverseSystem.firstDerivedLimit`;
- `bridge/view`: the functor-level tower `Ksys ⋙ HMod q` used to express the inverse limit of
  the cohomology sheaves.
-/

section

variable (X : RingedSite.{u, v})

local notation "ModX" => ModuleCat X
local notation "DModX" => ModuleDerived X
local notation "HMod" => DerivedCategory.homologyFunctor ModX

variable [IsGrothendieckAbelian (ModuleCat X)]
variable [HasWeakSheafify X.siteTopology AddCommGrpCat.{max u v}]

-- Proof sketch: for each `U ∈ B`, apply Lemma `21.23.11` to the derived-limit object `K` and use
-- the basiswise acyclicity of the cohomology sheaves to identify `H^q(U, K)` with
-- the degree-zero cohomology of the sheaf `𝓗[q](X, K)`. Apply Remark `21.23.4` to the tower
-- `RΓ(U, K_n)` and the vanishing of `R^1 lim_n Γ(U, 𝓗[q](X, K_n))`, expressed canonically by the
-- `firstDerivedLimit` of the sections tower
-- `Ksys ⋙ HMod q ⋙ moduleSectionsAsAbelianFunctor X U`, to identify
-- `H^q(U, K)` with the inverse limit of the sections of `𝓗[q](X, K_n)` over `U`. Since every object
-- admits a cover by members of `B`, the sheafification of this basiswise presheaf identity gives
-- the claimed isomorphism of cohomology sheaves.
/-- Lemma 21.23.12: let `X` be a ringed site, let `(K_n)` be an inverse system in
`D(𝒪_X)`, and let `K = R lim_n K_n` be a chosen derived limit. If a subset `B` of objects covers
the site, and if for a fixed `q ∈ ℤ` the cohomology sheaves `𝓗[q](X, K_n)` are basiswise acyclic
on `B` and the inverse systems `n ↦ Γ(U, 𝓗[q](X, K_n))` have vanishing `R^1 lim` for every
`U ∈ B`, then the `q`-th cohomology sheaf of `K` is isomorphic to the inverse limit of the tower
`n ↦ 𝓗[q](X, K_n)`. -/
@[stacks 0A09]
theorem derivedLimit_cohomologySheaf_isomorphic_limit_of_basiswise_acyclic
    (Ksys : ℕᵒᵖ ⥤ DModX)
    (K : DModX)
    (hK : IsDerivedLimit Ksys K)
    (B : Set X)
    (hcover : X.siteTopology.HasEnoughObjectsWithProperty (· ∈ B))
    (q : ℤ)
    (hacyclic : BasiswiseSingleAcyclic X B (Ksys ⋙ HMod q))
    (hR1lim : BasiswiseFirstDerivedLimitIsZero X B (Ksys ⋙ HMod q)) :
    IsIsomorphic
      (𝓗[q](X, K))
      (limit (Ksys ⋙ HMod q)) := sorry

end
