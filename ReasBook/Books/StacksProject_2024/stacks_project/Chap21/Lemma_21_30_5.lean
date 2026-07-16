import StacksProject_2024.stacks_project.Chap21.Lemma_21_7_2
import StacksProject_2024.stacks_project.Chap21.«21_30_0_1»
import StacksProject_2024.stacks_project.Chap21.Situation_21_30_1

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory Opposite
open CategoryTheory.Sheaf
open scoped CategoryTheory.GrothendieckTopology

noncomputable section

universe u

namespace CategoryTheory.GrothendieckTopology

variable {C : Type u} [Category.{u} C]
variable {τ τ' : GrothendieckTopology C}

/- Domain-style sampling for Lemma 21.30.5:
- primary domain: localized topology comparison on the slice sites `(C_τ / X)` and
  `(C_{τ'} / X)`, at the level of the degree-`n + 1` cohomology groups appearing in the Leray
  edge sequence for `ε_X`;
- sampled owner declarations:
  `CohomologyComparisonSituation.LocalVanishing`,
  `comparisonTopologyAdjunction`,
  `comparisonTopologyPullbackAb`,
  `comparisonTopologyPushforwardAb`,
  `Sheaf.sheafPushforwardContinuous_sectionsOverObjectDerivedIso`,
  `siteAbelianSectionsFunctor`,
  `Functor.rightDerived`;
- best owner abstraction:
  `source-facing`: the canonical degree-`n + 1` comparison morphism for `ε_X`, together with
    its injectivity under `(V_n)`;
  `core/canonical`: the chapter owner `(V_n)` given by
    `CohomologyComparisonSituation.LocalVanishing`, the localized topology-comparison adjunction
    `comparisonTopologyAdjunction AddCommGrpCat.{u} hle X`, the exact inverse-image functor
    `comparisonTopologyPullbackAb hle X`, the topology-comparison functor
    `comparisonTopologyPushforwardAb hle X`, and the sections owner
    `siteAbelianSectionsFunctor`, read through the owner-level right-derived comparison
    `Sheaf.sheafPushforwardContinuous_sectionsOverObjectDerivedIso`;
  `bridge/view`: the usual cohomology-group notation `H^{n + 1}` for the objectwise values of the
    right-derived terminal-sections owners on `(C_{τ'} / X)` and `(C_τ / X)`.

Primitive data versus derived API:
- primitive data: the comparison hypothesis `hle : τ' ≤ τ`, the comparison situation `h`, the
  object `X`, the sheaf `ℱ' : Sheaf (τ'.over X) AddCommGrpCat`, its membership `hℱ' : A' X ℱ'`,
  and the degree `n`;
- derived API: the canonical localized comparison morphism
  `H^{n + 1}(C_{τ'} / X, ℱ') ⟶ H^{n + 1}(C_τ / X, ε_X⁻¹ ℱ')`,
  spelled directly in the theorem statements by composing the localized adjunction unit with the
  canonical `21.7.2` cohomology comparison for `ε_X`.

This file should therefore reuse `CohomologyComparisonSituation.LocalVanishing` directly and keep
the source-facing injectivity/image theorem surface together with
`localizedComparisonLocallyZero` as the main public API, while the concrete comparison morphism
stays theorem-local and any pushforward-side comparison data remains internal to that term.
-/

section

variable (hle : τ' ≤ τ)
variable (X : C)

variable [HasWeakSheafify (τ.over X) AddCommGrpCat.{u}]
variable [HasSheafify (τ.over X) AddCommGrpCat.{u}]
variable [HasSheafify (τ'.over X) AddCommGrpCat.{u}]
variable [HasExt (Sheaf (τ.over X) AddCommGrpCat.{u})]
variable [HasExt (Sheaf (τ'.over X) AddCommGrpCat.{u})]

variable (ℱ' : Sheaf (τ'.over X) AddCommGrpCat.{u}) (n : ℕ)

/-- Source-facing local vanishing on the textbook codomain `H^{n + 1}(C_τ / X, ε_X⁻¹ ℱ')`,
written in Lean as cohomology at the terminal object of `(C_τ / X)`, with local triviality still
tested on a `τ'`-cover of `X`. -/
def localizedComparisonLocallyZero
    (ξ : ((ε[hle]_(X)⁻¹).obj ℱ').H' (n + 1) (Over.mk (𝟙 X))) : Prop :=
  ∃ T : (τ'.over X).Cover (Over.mk (𝟙 X)), ∀ I : T.Arrow,
    (((((ε[hle]_(X)⁻¹).obj ℱ').cohomologyPresheaf (n + 1)).map
        I.f.op) ξ = 0)

end

section

variable (hle : τ' ≤ τ)
variable (P : MorphismProperty C)
variable (A' : ∀ X : C, ObjectProperty (Sheaf (τ'.over X) AddCommGrpCat.{u}))

variable [∀ X : C, HasWeakSheafify (τ.over X) AddCommGrpCat.{u}]
variable [∀ X : C, HasSheafify (τ.over X) AddCommGrpCat.{u}]
variable [∀ X : C, HasSheafify (τ'.over X) AddCommGrpCat.{u}]
variable [∀ X : C, HasExt (Sheaf (τ.over X) AddCommGrpCat.{u})]
variable [∀ X : C, HasExt (Sheaf (τ'.over X) AddCommGrpCat.{u})]

-- Proof sketch: apply the Leray spectral sequence for the localized comparison morphism `ε_X`.
-- Under `(V_n)`, the positive-degree `E₂^{p,q}`-terms with `1 ≤ q ≤ n` vanish on `A'_X`, so the
-- edge map into total degree `n + 1` is injective. Compose that edge map with the canonical
-- `21.7.2` cohomology comparison for `ε_X` to obtain the source-facing comparison morphism into
-- the textbook codomain `H^{n + 1}(C_τ / X, ε_X⁻¹ ℱ')`; its image is exactly the locally trivial
-- classes there.
/-- Lemma 21.30.5: in Situation `21.30.1`, under the chapter's local vanishing condition
`(V_n)`, the canonical localized comparison morphism on degree `n + 1` cohomology is injective,
and its image in `H^{n + 1}(C_τ / X, ε_X⁻¹ ℱ')` consists exactly of the classes that become
trivial on a `τ'`-cover of `X`. -/
@[stacks 0EZC]
theorem localizedComparisonMap_injective_and_range_eq_locallyZero_of_localVanishingCondition
    (h : CohomologyComparisonSituation τ τ' P A')
    (X : C)
    (ℱ' : Sheaf (τ'.over X) AddCommGrpCat.{u})
    (hℱ' : A' X ℱ')
    (n : ℕ)
    (hVn : (V_n) h) :
    let comparisonMap :=
      (((cohomologyPresheafFunctor (τ'.over X) (n + 1)).map
          ((comparisonTopologyAdjunction AddCommGrpCat.{u} hle X).unit.app ℱ')).app
          (op (Over.mk (𝟙 X)))) ≫
        (letI : Functor.IsContinuous (𝟭 (Over X)) (τ'.over X) (τ.over X) :=
            comparisonOver_id_isContinuous hle X;
          sheafPushforwardContinuous_cohomologyAtObjectComparison
            (𝟭 (Over X)) ((ε[hle]_(X)⁻¹).obj ℱ') (n + 1) (Over.mk (𝟙 X)))
    Function.Injective comparisonMap ∧
      ∀ ξ : ((ε[hle]_(X)⁻¹).obj ℱ').H' (n + 1) (Over.mk (𝟙 X)),
        ξ ∈ Set.range comparisonMap ↔ localizedComparisonLocallyZero hle X ℱ' n ξ := by
  sorry

/-- Source-facing companion: under `(V_n)`, the image of the canonical localized comparison
morphism is exactly the locally trivial classes in
`H^{n + 1}(C_τ / X, ε_X⁻¹ ℱ')`. -/
theorem localizedComparisonMap_mem_range_iff_locallyZero_of_localVanishingCondition
    (h : CohomologyComparisonSituation τ τ' P A')
    (X : C)
    (ℱ' : Sheaf (τ'.over X) AddCommGrpCat.{u})
    (hℱ' : A' X ℱ')
    (n : ℕ)
    (hVn : (V_n) h)
    (ξ : ((ε[hle]_(X)⁻¹).obj ℱ').H' (n + 1) (Over.mk (𝟙 X))) :
    let comparisonMap :=
      (((cohomologyPresheafFunctor (τ'.over X) (n + 1)).map
          ((comparisonTopologyAdjunction AddCommGrpCat.{u} hle X).unit.app ℱ')).app
          (op (Over.mk (𝟙 X)))) ≫
        (letI : Functor.IsContinuous (𝟭 (Over X)) (τ'.over X) (τ.over X) :=
            comparisonOver_id_isContinuous hle X;
          sheafPushforwardContinuous_cohomologyAtObjectComparison
            (𝟭 (Over X)) ((ε[hle]_(X)⁻¹).obj ℱ') (n + 1) (Over.mk (𝟙 X)))
    ξ ∈ Set.range comparisonMap ↔
      localizedComparisonLocallyZero hle X ℱ' n ξ := by
  sorry

/-- Source-facing companion: under `(V_n)`, the canonical localized comparison morphism is
injective in degree `n + 1`. -/
theorem localizedComparisonMap_injective_of_localVanishingCondition
    (h : CohomologyComparisonSituation τ τ' P A')
    (X : C)
    (ℱ' : Sheaf (τ'.over X) AddCommGrpCat.{u})
    (hℱ' : A' X ℱ')
    (n : ℕ)
    (hVn : (V_n) h) :
    let comparisonMap :=
      (((cohomologyPresheafFunctor (τ'.over X) (n + 1)).map
          ((comparisonTopologyAdjunction AddCommGrpCat.{u} hle X).unit.app ℱ')).app
          (op (Over.mk (𝟙 X)))) ≫
        (letI : Functor.IsContinuous (𝟭 (Over X)) (τ'.over X) (τ.over X) :=
            comparisonOver_id_isContinuous hle X;
          sheafPushforwardContinuous_cohomologyAtObjectComparison
            (𝟭 (Over X)) ((ε[hle]_(X)⁻¹).obj ℱ') (n + 1) (Over.mk (𝟙 X)))
    Function.Injective comparisonMap := by
  sorry

end

end CategoryTheory.GrothendieckTopology
