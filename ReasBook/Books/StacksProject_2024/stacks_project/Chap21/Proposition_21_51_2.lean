import StacksProject_2024.Chap07.Definition_7_40_2
import StacksProject_2024.Chap13.Remark_13_34_5
import StacksProject_2024.Chap15.Lemma_15_87_10
import StacksProject_2024.Chap19.Lemma_19_13_4

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.SequentialInverseSystem
open Opposite
open DerivedCategory

noncomputable section

universe w v u

attribute [local instance] HasDerivedCategory.standard

namespace CategoryTheory

section

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
variable (𝒪 : Sheaf J RingCat.{max u v})

local notation "ModO" => SheafOfModules 𝒪
local notation "DModO" => DerivedCategory ModO
local notation "Q" => (DerivedCategory.Q : CochainComplex ModO ℤ ⥤ DModO)
local notation "single0" => DerivedCategory.singleFunctor ModO (0 : ℤ)
local notation "H" => DerivedCategory.homologyFunctor ModO

local instance sheafOfModulesAbelian : Abelian ModO :=
  SheafOfModules.instAbelian 𝒪

local instance sheafOfModulesHasCountableProducts : HasCountableProducts ModO where
  out T := by infer_instance

local instance sheafOfModulesHasLimitsOfShape : HasLimitsOfShape ℕᵒᵖ ModO :=
  inferInstance

variable (B : Set C)

/- Domain-style sampling for Proposition 21.51.2:
- primary domain: sheaves of modules on a site with a covering family of weakly contractible
  objects, together with derived inverse limits and Milnor exact sequences;
- sampled owner declarations:
  `GrothendieckTopology.HasEnoughObjectsWithProperty`,
  `SheafOfModules.evaluation`,
  `CategoryTheory.SequentialInverseSystem`,
  `CategoryTheory.AB4Star`,
  `CategoryTheory.derivedCategory_Q_preserves_product_of_ab4Star`,
  `CategoryTheory.derivedCategory_product_isLimit_of_termwise_products_of_kInjective`,
  `CategoryTheory.derivedCategory_hasProductsOfShape`,
  `CategoryTheory.IsTruncationDerivedLimitComparison`,
  `CategoryTheory.SequentialInverseSystem.firstDerivedLimit`,
  `CategoryTheory.derivedLimit_cohomology_shortExact`,
  `CategoryTheory.ShortComplex.pi_homologyIso`;
- best owner abstraction: this file is `source-facing`; the supporting canonical owners are the
  site-level cover-existence owner
  `J.HasEnoughObjectsWithProperty (J.IsWeaklyContractible)`,
  module-valued sections functor `SheafOfModules.evaluation 𝒪 (op U)`, the exact-products owner
  `AB4Star ModO` and the corresponding
  preservation theorem `derivedCategory_Q_preserves_product_of_ab4Star` used in clause `(5)`,
  together with the K-injective bridge
  `derivedCategory_product_isLimit_of_termwise_products_of_kInjective`, the
  truncation-comparison predicate `IsTruncationDerivedLimitComparison`, and the Milnor
  `R^1 lim` owners `SequentialInverseSystem.firstDerivedLimit` and
  `derivedLimit_cohomology_shortExact`;
- primitive-vs-derived split:
  primitive data are `𝒪`, the chosen basis `B` together with its weak-contractibility hypothesis
  and cover-existence owner in clause `(1)`, the canonical site-level owner
  `J.HasEnoughObjectsWithProperty (J.IsWeaklyContractible)` in clauses `(2)` through `(4)`, and
  the chosen sequential towers or comparison morphisms in clauses `(3)` and `(6)` through `(8)`;
  derived API consists of the internal additive-sections bridge used to prove part `(1)`, the ambient product
  computation from arbitrary representative complexes in part `(5)`, and the Milnor
  `firstDerivedLimit`/short-exact-sequence owners in parts `(7)` and `(8)`.

Source/core/bridge triage:
- `source-facing`: the eight proposition clauses;
- `core/canonical`: `J.HasEnoughObjectsWithProperty (J.IsWeaklyContractible)`,
  `SheafOfModules.evaluation`, `AB4Star`, `derivedCategory_Q_preserves_product_of_ab4Star`,
  `derivedCategory_hasProductsOfShape`,
  `derivedCategory_product_isLimit_of_termwise_products_of_kInjective`,
  `IsTruncationDerivedLimitComparison`, `SequentialInverseSystem.firstDerivedLimit`,
  `derivedLimit_cohomology_shortExact`, and the standard derived-category owners;
- `bridge/view`: forgetting the `𝒪(U)`-module structure on
  `(SheafOfModules.evaluation 𝒪 (op U)).obj _` to `AddCommGrpCat`, and the Chapter 19 K-injective
  product theorem used to prove the source-facing product statement in clause `(5)`. -/

-- Proof sketch: on each `U ∈ B`, weak contractibility makes the sections functor exact on short
-- complexes. The forward implication maps an exact short complex along that exact functor. For
-- the converse, exactness of sheaf-module morphisms can be checked after restricting to a
-- covering by basis objects in `B`.
/-- Proposition 21.51.2 (1): if `B` is a covering family of weakly contractible objects of the
site `(C, J)`, then a short complex of `𝒪`-modules is exact if and only if its
module-valued section sequence over every `U ∈ B` is exact. -/
@[stacks 0947]
theorem shortComplex_exact_iff_exact_on_basis_sections
    (hweak : ∀ ⦃U : C⦄, U ∈ B → J.IsWeaklyContractible U)
    (hcover : J.HasEnoughObjectsWithProperty (· ∈ B))
    (S : ShortComplex ModO) :
    S.Exact ↔
      ∀ ⦃U : C⦄, U ∈ B →
        (S.map (SheafOfModules.evaluation 𝒪 (op U))).Exact := sorry

-- Proof sketch: the weakly contractible basis gives the vanishing criterion needed for the
-- canonical truncation map `K ⟶ R lim_n τ_{≥ -n} K`. Applying the truncation-tower Milnor
-- criterion to any compatible comparison map yields that comparison as an isomorphism.
/-- Proposition 21.51.2 (2): if the site `(C, J)` has enough weakly contractible
objects, then every compatible comparison map from `K` to a chosen derived limit of the
truncation tower `(τ_{≥ -n} K)_n` is an isomorphism. This is the Lean form of the statement
`K = R lim_n τ_{≥ -n} K`. -/
@[stacks 0947]
theorem truncationComparison_isIso_of_hasEnoughWeaklyContractibleObjects
    (hEnough : J.HasEnoughObjectsWithProperty (J.IsWeaklyContractible))
    (K L : DModO) (c : K ⟶ L)
    (hc : IsTruncationDerivedLimitComparison K L c) :
    IsIso c := sorry

-- Proof sketch: evaluating on weakly contractible objects supplied by `hEnough` reduces the
-- statement to the corresponding surjectivity statement for inverse limits of towers of abelian
-- groups with surjective transition maps. Local surjectivity on such a cover then promotes to
-- surjectivity of the sheaf-module map.
/-- Proposition 21.51.2 (3): if the site `(C, J)` has enough weakly contractible
objects and `(ℱ_n)_n` is an inverse system of `𝒪`-modules with surjective
transition maps, then the projection `lim_n ℱ_n ⟶ ℱ_0` is surjective.
In Lean, the first stage is indexed by `0`. -/
@[stacks 0947]
theorem limit_projectionToFirst_epi_of_surjective_transitions_of_hasEnoughWeaklyContractibleObjects
    (hEnough : J.HasEnoughObjectsWithProperty (J.IsWeaklyContractible))
    (Fsys : SequentialInverseSystem ModO)
    (hsurj : ∀ n : ℕ, Epi (Fsys.stepMap n)) :
    Epi (limit.π Fsys (op 0)) := sorry

-- Proof sketch: choose a covering family of weakly contractible objects from `hEnough` and use
-- part `(1)` to test exactness of a product short complex on sections over those basis objects.
-- Products in `AddCommGrpCat` are exact, so the product short complex is exact on every chosen
-- basis object, hence exact in `Mod(𝒪)`.
/-- Proposition 21.51.2 (4): if the site `(C, J)` has enough weakly contractible
objects, then products are exact in the abelian category `Mod(𝒪)`. -/
@[stacks 0947]
theorem siteModuleCat_ab4Star_of_hasEnoughWeaklyContractibleObjects
    [HasProducts ModO]
    (hEnough : J.HasEnoughObjectsWithProperty (J.IsWeaklyContractible))
    :
    AB4Star ModO := sorry

/-- Companion instance for Proposition 21.51.2 (4): enough weakly contractible objects give exact
products in `ModO`, so the Chapter 19 exact-products API applies by typeclass search. -/
instance instAB4StarSiteModuleCatOfHasEnoughWeaklyContractibleObjects
    [HasProducts ModO]
    [Fact (J.HasEnoughObjectsWithProperty (J.IsWeaklyContractible))] :
    AB4Star ModO := by
  exact siteModuleCat_ab4Star_of_hasEnoughWeaklyContractibleObjects J 𝒪 Fact.out

-- Proof sketch: part `(4)` gives exact products in `Mod(𝒪)`. Replacing the
-- chosen representative complexes by quasi-isomorphic K-injective ones, Chapter 19 identifies the
-- termwise product of those replacements with the product in the derived category. Exactness of
-- products then lets one compare the original termwise product complex with the K-injective one,
-- so the original termwise product already satisfies the same universal property.
section

variable [HasProducts ModO] [Fact (J.HasEnoughObjectsWithProperty (J.IsWeaklyContractible))]
variable {T : Type w} (I : T → CochainComplex ModO ℤ)

/- Proposition 21.51.2 (5): if the site `(C, J)` has enough weakly contractible
objects, then products in `D(𝒪)` can be computed from the termwise product of any chosen
representative complexes. In Lean this is the canonical Chapter 19 owner
`derivedCategory_Q_preserves_product_of_ab4Star`, specialized to `Mod(𝒪)` and supplied with the
`AB4Star ModO` instance from Proposition 21.51.2 (4). -/
recall derivedCategory_Q_preserves_product_of_ab4Star
set_option linter.hashCommand false in
#check (derivedCategory_Q_preserves_product_of_ab4Star I :
  PreservesLimit (Discrete.functor I) Q)

end

-- Proof sketch: apply the Milnor short exact sequence in degree `p` to the chosen derived limit
-- of the degree-zero tower `(ℱ_n[0])_n`. Since `H^q(ℱ_n[0]) = 0` for every
-- `q ≠ 0`, both adjacent terms vanish when `p > 1`, forcing `H^p(K) = 0`.
/-- Proposition 21.51.2 (6): if `K = R lim_n ℱ_n[0]` is a chosen derived limit
of a tower of `𝒪`-modules, then `R^p lim_n ℱ_n = 0` for every
`p > 1`. In Lean, this is the vanishing of the cohomology objects `H^p(K)` for `p > 1`. -/
@[stacks 0947]
theorem moduleTower_derivedLimit_higherHomology_isZero
    (Fsys : SequentialInverseSystem ModO)
    (K : DModO)
    (hK : IsDerivedLimit (Fsys ⋙ single0) K)
    (p : ℤ) (hp : 1 < p) :
    IsZero ((H p).obj K) := sorry

-- Proof sketch: specialize the Milnor short exact sequence to degree `1` for the same degree-zero
-- tower. The left term is already the canonical owner `Fsys.firstDerivedLimit`, so the sequence
-- identifies `H^1(K)` with that object.
/-- Proposition 21.51.2 (7): if `K = R lim_n ℱ_n[0]` is a chosen derived limit
of a tower of `𝒪`-modules, then `R^1 lim_n ℱ_n` is represented by the
canonical first derived inverse-limit object of the tower. -/
@[stacks 0947]
theorem moduleTower_homologyOne_iso_firstDerivedLimit
    (Fsys : SequentialInverseSystem ModO)
    (K : DModO)
    (hK : IsDerivedLimit (Fsys ⋙ single0) K) :
    IsIsomorphic ((H (1 : ℤ)).obj K) Fsys.firstDerivedLimit :=
  sorry

/- Proposition 21.51.2 (8): for a sequential inverse system in `D(𝒪)` and a chosen
derived limit `K = R lim_n K_n`, the Milnor short exact sequence
`0 ⟶ R^1 lim_n H^{p-1}(K_n) ⟶ H^p(K) ⟶ lim_n H^p(K_n) ⟶ 0`
is already the canonical Chapter 15 owner theorem
`derivedLimit_cohomology_shortExact`; the weakly-contractible-basis hypotheses do
not enter this statement. -/
recall derivedLimit_cohomology_shortExact

end

end CategoryTheory
