import StacksProject_2024.Chap13.Lemma_13_34_6
import StacksProject_2024.Chap21.Lemma_21_23_10

open CategoryTheory
open CategoryTheory.Limits
open DerivedCategory
open Opposite
open RingedSite.Hom
open scoped RingedSiteCohomology

noncomputable section

universe u v

attribute [local instance] HasDerivedCategory.standard

section

variable (X : RingedSite.{u, v})

local notation "ModX" => ModuleCat X

variable [CategoryWithHomology (ModuleCat X)]
variable [IsGrothendieckAbelian.{max u v} (ModuleCat X)]
variable [HasWeakSheafify X.siteTopology AddCommGrpCat.{max u v}]
variable [HasCountableProducts (ModuleCat X)]

/- Domain-style sampling for Lemma 21.24.1:
- primary domain: lower-truncation inverse-limit comparisons in `D(𝒪)` on a ringed site,
  together with the uniform basiswise vanishing criterion for negative cohomology sheaves;
- sampled owner declarations:
  `LowerTruncationResolutionSystem.fromSource`,
  `LowerTruncationResolutionSystem.intoLimit`,
  `LowerTruncationResolutionSystem.intoLimit_comp_π`,
  `CategoryTheory.GrothendieckTopology.HasEnoughObjectsWithProperty`,
  `RingedSite.Hom.cohomologyOverObject`,
  `RingedSite.Hom.cohomologySheaf`,
  `truncationComparison_isIso_of_uniform_basiswise_negative_cohomologySheaf_vanishing`;
- best owner abstraction: the chosen inverse-system data is already owned by
  `LowerTruncationResolutionSystem`, so the public statement should use the canonical stage maps
  `S.fromSource n` and the canonical map `S.intoLimit`, while the basis-cover and cohomology
  hypotheses should use the Chapter 21 owners
  `X.siteTopology.HasEnoughObjectsWithProperty (· ∈ B)` and
  `UniformBasiswiseNegativeCohomologySheafVanishing X (Q.obj F) d B`
  directly instead of local wrapper predicates;
- primitive-vs-derived split:
  primitive data: the complex `F`, the chosen lower truncation injective system `S`, the subset
  `B`, the bound `d`, and the stagewise compatibility of a map `γ : F ⟶ lim S.diagram`;
  derived API: the canonical owner map `S.intoLimit` and the reduction from a compatible map on
    the inverse limit to the Chapter 13/21 comparison criteria.

Source/core/bridge triage:
- `source-facing`: the quasi-isomorphism criterion for any compatible comparison
  `γ : F^• ⟶ lim I_n^•`;
- `core/canonical`: `LowerTruncationResolutionSystem`, `S.fromSource`, `S.intoLimit`, and the
  Chapter 21 truncation-comparison criterion in the derived category;
- `bridge/view`: the specialization from the arbitrary compatible comparison `γ` to the canonical
  map `S.intoLimit`. -/

/-- A stagewise compatible map `γ : F^• ⟶ lim I_n^•` induces the Chapter 13
derived-limit-comparison predicate on `Q.map γ`. -/
theorem qMap_isLowerTruncationDerivedLimitComparison_of_comp_π
    (F : CochainComplex ModX ℤ)
    (S : LowerTruncationResolutionSystem (isInjective ModX) F)
    (γ : F ⟶ limit S.diagram)
    (hγ : ∀ n : ℕ, γ ≫ limit.π S.diagram (op n) = S.fromSource n) :
    IsLowerTruncationDerivedLimitComparison F
      (Q.obj (limit S.diagram)) (Q.map γ) := by
  sorry

/-- Canonical owner companion for Lemma 21.24.1, specialized to the map `S.intoLimit`. -/
theorem intoLimit_quasiIso_of_uniform_basiswise_negative_cohomologySheaf_vanishing
    (F : CochainComplex ModX ℤ)
    (S : LowerTruncationResolutionSystem (isInjective ModX) F)
    (B : Set X)
    (d : ℕ)
    (hcover : X.siteTopology.HasEnoughObjectsWithProperty (· ∈ B))
    (hvanish : UniformBasiswiseNegativeCohomologySheafVanishing X (Q.obj F) d B) :
    QuasiIso S.intoLimit := by
  sorry

/-- Lemma 21.24.1: let `(𝒞, 𝒪)` be a ringed site, let `F^•` be a complex of `𝒪`-modules, and
let `γ : F^• ⟶ lim I_n^•` be a stagewise compatible map to the inverse limit of a chosen lower
truncation injective system. If every object admits a covering by members of `B` and
`H^p(U, H^q(F^•)) = 0` for `p > d`, `q < 0`, and `U ∈ B`, then `γ` is a quasi-isomorphism. -/
@[stacks 070Q]
theorem
    lowerTruncationResolutionLimit_comparison_quasiIso_of_uniform_basiswise_negative_cohomologySheaf_vanishing
    (F : CochainComplex ModX ℤ)
    (S : LowerTruncationResolutionSystem (isInjective ModX) F)
    (γ : F ⟶ limit S.diagram)
    (B : Set X)
    (d : ℕ)
    (hγ : ∀ n : ℕ, γ ≫ limit.π S.diagram (op n) = S.fromSource n)
    (hcover : X.siteTopology.HasEnoughObjectsWithProperty (· ∈ B))
    (hvanish : UniformBasiswiseNegativeCohomologySheafVanishing X (Q.obj F) d B) :
    QuasiIso γ := by
  have hc :
      IsLowerTruncationDerivedLimitComparison F
        (Q.obj (limit S.diagram)) (Q.map γ) :=
    qMap_isLowerTruncationDerivedLimitComparison_of_comp_π X F S γ hγ
  have hQγ : IsIso (Q.map γ) := by
    exact
      (lowerTruncationResolutionLimit_quasiIso_iff_isIso_derivedComparison S hc).1
        (intoLimit_quasiIso_of_uniform_basiswise_negative_cohomologySheaf_vanishing
          X F S B d hcover hvanish)
  exact (DerivedCategory.isIso_Q_map_iff_quasiIso ModX γ).1 hQγ

end
