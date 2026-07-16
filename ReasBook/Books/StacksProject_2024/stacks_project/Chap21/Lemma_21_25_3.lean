import StacksProject_2024.stacks_project.Chap13.Definition_13_34_1
import StacksProject_2024.stacks_project.Chap13.Lemma_13_17_1
import StacksProject_2024.stacks_project.Chap21.Lemma_21_20_3
import StacksProject_2024.stacks_project.Chap21.Situation_21_25_1

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open CategoryTheory.ObjectProperty
open CategoryTheory.SequentialInverseSystem
open Opposite (op)
open CategoryTheory.GrothendieckTopology (BoundedCohomologyBasis)
open DerivedCategory.TStructure
open scoped DerivedCategoryWithCohomologyIn
open scoped RingedSiteCohomology

noncomputable section

universe u v

attribute [local instance] HasDerivedCategory.standard

section

variable (X : RingedSite.{u, v})
variable [HasSheafify X.siteTopology AddCommGrpCat]
variable [HasExt (Sheaf X.siteTopology AddCommGrpCat)]

local notation "ModX" => SheafOfModules X.structureSheaf
local notation "DModX" => DerivedCategory ModX

variable [Abelian ModX]
variable [CategoryWithHomology ModX]
variable [IsGrothendieckAbelian ModX]

variable (A : ObjectProperty ModX)

local notation "plusAι" =>
  (ObjectProperty.ι (derivedCategoryBoundedBelowCohomologyInProperty A) :
    D⁺_{A} ⥤ boundedBelowDerivedCategory ModX)

local notation "plusι" =>
  (ObjectProperty.ι (t.plus : ObjectProperty DModX) :
    boundedBelowDerivedCategory ModX ⥤ DModX)

local notation "H" => DerivedCategory.homologyFunctor ModX
local notation "Dlim[" Ksys "]" => Ksys ⋙ plusAι ⋙ plusι
local notation "Hlim[" Ksys "," j "]" => Dlim[Ksys] ⋙ H j

/- Domain-style sampling for Lemma 21.25.3:
- primary domain: sequential derived inverse limits in the ambient derived category `DModX`
  on a ringed site,
  specialized to the bounded-below cohomology-in owner `D⁺_{A}` and to the module-valued
  cohomology sheaf owner `𝓗[j](X, -)`;
- sampled owner declarations:
  `RingedSite.Hom.ModuleCat`,
  `RingedSite.Hom.ModuleDerived`,
  `RingedSite.Hom.cohomologySheaf`,
  `CategoryTheory.derivedCategoryBoundedBelowCohomologyInProperty`,
  `CategoryTheory.DerivedCategoryPlusWithCohomologyIn.toDerived`,
  `CategoryTheory.IsDerivedLimit`,
  `CategoryTheory.SequentialInverseSystem.transitionMap`;
- best owner abstraction: the source-facing tower belongs in `D⁺_{A}` rather than being
  represented as a bare functor into `D⁺_{A}` or as a raw tower in `DModX` together
  with separate bounded-below and
  cohomology-membership hypotheses; the degree-`j` cohomology tower should be written as the
  canonical sequential inverse system obtained by postcomposing the standard inclusion
  `D⁺_{A} ⥤ boundedBelowDerivedCategory ModX ⥤ DModX` with
  `DerivedCategory.homologyFunctor`, and its stabilization should be stated by the
  source-faithful tail condition on the owner transition maps
  `H^j(K_n) ⟶ H^j(K_{n₀})`; on `ℕᵒᵖ`, the canonical bridge owner is
  `Functor.IsEventuallyConstantTo (op n₀)`;
- primitive data: the ringed site `X`, the object property `A`, the bounded-cohomology basis,
  the tower `Ksys : SequentialInverseSystem D⁺_{A}`, the chosen derived limit `K`, the
  eventual-value sheaf `ℋj`, the stabilization index `n₀`, and the degree `j`; the weak-Serre
  closure data are not primitive inputs for this statement because neither the basis nor the
  bounded-below cohomology-in owner `D⁺_{A}` stores them here;
- derived API: the inclusion `D⁺_{A} ⥤ boundedBelowDerivedCategory ModX ⥤ DModX` and the ambient
  degree-`j` cohomology sheaf owner, together with the induced cohomology tower given by
  postcomposition with `DerivedCategory.homologyFunctor` and its canonical transition maps.

Source/core/bridge triage:
- `source-facing`: the eventual-constancy comparison theorem below;
- `core/canonical`: `ModuleCat`, `ModuleDerived`, `𝓗[j](X, -)`,
  `derivedCategoryBoundedBelowCohomologyInProperty`, `D⁺_{A}`, `IsDerivedLimit`, and
  `SequentialInverseSystem.transitionMap`;
- `bridge/view`: the canonical inclusion
  from the bounded-below cohomology-in tower to the ambient derived category, expressed on
  objects by `K ↦ K.toDerived`; the induced cohomology-sheaf tower is expressed directly by
  postcomposition with `DerivedCategory.homologyFunctor`. -/

-- Proof sketch: use the bounded-cohomology basis from Situation `21.25.1` to reduce to basis
-- objects with uniformly bounded higher cohomology for `A`-valued sheaves. For a fixed degree `j`
-- and basis object `V`, compare the spectral sequences computing `H^*(V, K_n)` from the
-- cohomology sheaves `H^q(K_n)`; bounded-below hypotheses and eventual constancy of the
-- degree-`j` cohomology tower via its transition maps force the groups `H^(j-1)(V, K_n)` and
-- `H^j(V, K_n)` to stabilize. Lemma
-- `21.23.6` then gives injectivity of the Milnor comparison map on the cohomology sheaf of
-- `R lim K_n`, and Lemmas `21.20.3` and `21.23.2` give surjectivity after passing to a covering,
-- yielding the claimed identification of cohomology sheaves.
/-- Source-to-canonical bridge for Lemma 21.25.3: if all transition maps
`H^j(K_n) ⟶ H^j(K_{n₀})` are isomorphisms for `n ≥ n₀`, then the degree-`j` cohomology tower is
eventually constant in the canonical cofiltered sense. -/
lemma derivedLimit_cohomologyTower_isEventuallyConstantTo_of_transitionMap_isIso
    (Ksys : SequentialInverseSystem D⁺_{A})
    (j : ℤ)
    (n₀ : ℕ)
    (htransition_isIso :
      ∀ n : ℕ, ∀ hn : n₀ ≤ n,
        IsIso ((Hlim[Ksys,j]).transitionMap hn)) :
    (Hlim[Ksys,j]).IsEventuallyConstantTo (op n₀) := by
  sorry

/-- Canonical-to-source bridge for Lemma 21.25.3: eventual constancy of the degree-`j`
cohomology tower forces each transition map to the stage `n₀` to be an isomorphism. -/
instance derivedLimit_cohomology_transitionMap_isIso_of_isEventuallyConstantTo
    (Ksys : SequentialInverseSystem D⁺_{A})
    (j : ℤ)
    (n₀ : ℕ)
    {n : ℕ}
    [heventually_constant :
      (Hlim[Ksys,j]).IsEventuallyConstantTo (op n₀)]
    (hn : n₀ ≤ n) :
    IsIso ((Hlim[Ksys,j]).transitionMap hn) :=
  Functor.IsEventuallyConstantTo.isIso_map
    heventually_constant ((homOfLE hn).op) (𝟙 (op n₀))

/-- Bridge companion to Lemma 21.25.3: if the degree-`j` cohomology tower of `(K_n)` is
eventually constant from stage `n₀` on in the canonical cofiltered sense, then the degree-`j`
cohomology sheaf of the derived limit is already canonically isomorphic to the stage
`H^j(K_{n₀})`. -/
lemma derivedLimit_cohomology_isomorphic_stage_of_eventually_constant
    (basis : BoundedCohomologyBasis X.structureSheaf A)
    (Ksys : SequentialInverseSystem D⁺_{A})
    (K : DModX)
    (hK : IsDerivedLimit Dlim[Ksys] K)
    (j : ℤ)
    (n₀ : ℕ)
    (heventually_constant :
      (Hlim[Ksys,j]).IsEventuallyConstantTo (op n₀)) :
    IsIsomorphic (𝓗[j](X, K)) ((Hlim[Ksys,j]).obj (op n₀)) := by
  sorry

/-- Canonical eventual-constancy companion to Lemma 21.25.3: if the degree-`j` cohomology tower
is eventually constant from stage `n₀` on and its value at stage `n₀` is isomorphic to `ℋj`,
then the degree-`j` cohomology sheaf of the derived limit is isomorphic to `ℋj`. -/
lemma derivedLimit_cohomology_isomorphic_of_isEventuallyConstantTo
    (basis : BoundedCohomologyBasis X.structureSheaf A)
    (Ksys : SequentialInverseSystem D⁺_{A})
    (K : DModX)
    (hK : IsDerivedLimit Dlim[Ksys] K)
    (j : ℤ)
    (n₀ : ℕ)
    (ℋj : ModX)
    (hℋj :
      IsIsomorphic ((Hlim[Ksys,j]).obj (op n₀)) ℋj)
    (heventually_constant :
      (Hlim[Ksys,j]).IsEventuallyConstantTo (op n₀)) :
    IsIsomorphic (𝓗[j](X, K)) ℋj := by
  sorry

/-- Lemma 21.25.3: in Situation `21.25.1`, let `(K_n)` be a sequential inverse system in
`D⁺_{A}` and let `K` be a derived limit of this tower. Fix a degree `j`
and a stage `n₀`, and assume the transition maps `H^j(K_n) ⟶ H^j(K_{n₀})` are isomorphisms for
all `n ≥ n₀`, with `H^j(K_{n₀}) ≅ ℋj`. Then the
degree-`j` cohomology sheaf of the derived limit `K` is isomorphic to `ℋj`. -/
@[stacks 0D6T]
lemma derivedLimit_cohomology_isomorphic_of_eventually_constant
    (basis : BoundedCohomologyBasis X.structureSheaf A)
    (Ksys : SequentialInverseSystem D⁺_{A})
    (K : DModX)
    (hK : IsDerivedLimit Dlim[Ksys] K)
    (j : ℤ)
    (n₀ : ℕ)
    (ℋj : ModX)
    (hℋj :
      IsIsomorphic ((Hlim[Ksys,j]).obj (op n₀)) ℋj)
    (htransition_isIso :
      ∀ n : ℕ, ∀ hn : n₀ ≤ n,
        IsIso ((Hlim[Ksys,j]).transitionMap hn)) :
    IsIsomorphic (𝓗[j](X, K)) ℋj := by
  sorry

end
