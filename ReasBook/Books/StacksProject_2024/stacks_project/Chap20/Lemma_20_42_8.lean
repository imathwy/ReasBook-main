import StacksProject_2024.Chap20.«20_42_8_1»

-- Declarations for this item will be appended below by the statement pipeline.

open AlgebraicGeometry
open CategoryTheory
open CategoryTheory.MonoidalCategory
open CategoryTheory.MonoidalClosed

noncomputable section

universe u

attribute [local instance] HasDerivedCategory.standard

namespace AlgebraicGeometry.RingedSpace

/- Domain-style sampling for Lemma 20.42.8:
- primary domain: the closed monoidal derived category `D(𝒪_X)` and its tensor-internal-Hom
  adjunction;
- sampled owner declarations:
  `RingedSpaceDerived`,
  `MonoidalClosed.uncurry'`,
  `MonoidalClosed.uncurry`,
  `ringedSpaceDerivedEvaluationHom`;
- best owner abstraction: the canonical owner `MonoidalClosed.uncurry'` for the map
  `H^0(X, RHom(L, M)) → Hom_{D(𝒪_X)}(L, M)`, with
  `ringedSpaceDerivedEvaluationHom` supplying the source-facing comparison
  `M ⊗ L^∨ ⟶ RHom(L, M)`;
- primitive data: the braided monoidal closed structure on `RingedSpaceDerived X` and the objects
  `L`, `M`;
- derived API: the induced degree-zero global-sections map
  `H^0(X, M ⊗ L^∨) → Hom_{D(𝒪_X)}(L, M)`.

Source/core/bridge triage:
- `source-facing`: `ringedSpaceDerivedEvaluationH0ToHom`;
- `core/canonical`: `MonoidalClosed.uncurry'`;
- `bridge/view`: postcomposition with `ringedSpaceDerivedEvaluationHom L M`, followed by the
  owner bijection `H^0(X, RHom(L, M)) ≃ Hom(L, M)`.

This file therefore stays at the `bridge/view` layer: it should reuse the chapter adjunction owner
directly instead of rebuilding the same `H^0(RHom) → Hom` map from a fresh
unit-unwinding wrapper. -/

section

variable {X : RingedSpace.{u}}

variable [MonoidalCategory (RingedSpaceDerived X)]
variable [BraidedCategory (RingedSpaceDerived X)]
variable [MonoidalClosed (RingedSpaceDerived X)]

local notation "DModX" => RingedSpaceDerived X

private abbrev postcomposeHom (A : DModX) {B C : DModX} (f : B ⟶ C) : (A ⟶ B) ⟶ (A ⟶ C) :=
  fun g ↦ g ≫ f

/-- Lemma 20.42.8: for `L, M ∈ D(𝒪_X)`, the canonical morphism
`M ⊗ L^∨ ⟶ L ⟹ M` from `20.42.8.1` induces a canonical map
`H^0(X, M ⊗ L^∨) → (L ⟶ M)`.
In Lean, `H^0(X, K)` is modeled by morphisms `𝟙_ DModX ⟶ K`, where the monoidal unit `𝟙_ DModX`
is the structure-sheaf object of `D(𝒪_X)`. -/
@[stacks 08I1]
noncomputable def ringedSpaceDerivedEvaluationH0ToHom
    (L M : DModX) :
    (𝟙_ DModX ⟶ M ⊗ L^∨) ⟶ (L ⟶ M) :=
  fun s ↦
    MonoidalClosed.uncurry' (s ≫ ringedSpaceDerivedEvaluationHom L M)

/-- The bridge of Lemma 20.42.8 is definitionally the canonical owner
`MonoidalClosed.uncurry'` applied after postcomposition with
`ringedSpaceDerivedEvaluationHom L M`. -/
theorem ringedSpaceDerivedEvaluationH0ToHom_def
    (L M : DModX) :
    ringedSpaceDerivedEvaluationH0ToHom L M =
      fun s ↦ MonoidalClosed.uncurry' (s ≫ ringedSpaceDerivedEvaluationHom L M) := by
  rfl

/-- Evaluating the canonical map of Lemma 20.42.8 at a degree-zero class `s` amounts to
applying `MonoidalClosed.uncurry'` after postcomposing `s` with
`ringedSpaceDerivedEvaluationHom L M`. -/
@[simp] theorem ringedSpaceDerivedEvaluationH0ToHom_apply
    (L M : DModX) (s : 𝟙_ DModX ⟶ M ⊗ L^∨) :
    ringedSpaceDerivedEvaluationH0ToHom L M s =
      MonoidalClosed.uncurry' (s ≫ ringedSpaceDerivedEvaluationHom L M) := by
  simpa using congrFun (ringedSpaceDerivedEvaluationH0ToHom_def L M) s

/-- Currying the degree-zero comparison of Lemma 20.42.8 recovers postcomposition with the
canonical morphism `M ⊗ L^∨ ⟶ L ⟹ M`. -/
@[simp] theorem curry'_ringedSpaceDerivedEvaluationH0ToHom
    (L M : DModX) (s : 𝟙_ DModX ⟶ M ⊗ L^∨) :
    MonoidalClosed.curry' (ringedSpaceDerivedEvaluationH0ToHom L M s) =
      s ≫ ringedSpaceDerivedEvaluationHom L M := by
  simp [ringedSpaceDerivedEvaluationH0ToHom]

/-- The induced map on `H^0(X, -)` is functorial in the target object `M`. -/
theorem ringedSpaceDerivedEvaluationH0ToHom_natural
    (L : DModX) {M M' : DModX} (f : M ⟶ M') :
    CommSq
      (fun s : 𝟙_ DModX ⟶ M ⊗ L^∨ ↦ s ≫ (f ⊗ₘ 𝟙 L^∨))
      (ringedSpaceDerivedEvaluationH0ToHom L M)
      (ringedSpaceDerivedEvaluationH0ToHom L M')
      (postcomposeHom L f) := by
  refine CommSq.mk ?_
  funext s
  -- Proof comment: first prove functoriality of the source-facing evaluation morphism, then
  -- transport it through the canonical owner map `MonoidalClosed.uncurry'`.
  have hs :
      (s ≫ (f ⊗ₘ 𝟙 (L^∨))) ≫ ringedSpaceDerivedEvaluationHom L M' =
        (s ≫ ringedSpaceDerivedEvaluationHom L M) ≫ (ihom L).map f := by
    -- Proof comment: postcompose the target-side naturality statement with the chosen section `s`.
    simpa [Category.assoc] using
      congrArg (fun k ↦ s ≫ k) (ringedSpaceDerivedEvaluationHom_natural_target_assoc L f)
  apply MonoidalClosed.curry'_injective
  calc
    MonoidalClosed.curry'
        (ringedSpaceDerivedEvaluationH0ToHom L M' (s ≫ (f ⊗ₘ 𝟙 (L^∨)))) =
          (s ≫ (f ⊗ₘ 𝟙 (L^∨))) ≫ ringedSpaceDerivedEvaluationHom L M' := by
            rw [curry'_ringedSpaceDerivedEvaluationH0ToHom]
    _ = (s ≫ ringedSpaceDerivedEvaluationHom L M) ≫ (ihom L).map f := hs
    _ = MonoidalClosed.curry' (ringedSpaceDerivedEvaluationH0ToHom L M s) ≫ (ihom L).map f := by
          rw [curry'_ringedSpaceDerivedEvaluationH0ToHom]
    _ = MonoidalClosed.curry' (ringedSpaceDerivedEvaluationH0ToHom L M s ≫ f) := by
          rw [MonoidalClosed.curry'_ihom_map]

/-- Pointwise form of `ringedSpaceDerivedEvaluationH0ToHom_natural`. -/
theorem ringedSpaceDerivedEvaluationH0ToHom_natural_apply
    (L : DModX) {M M' : DModX} (f : M ⟶ M')
    (s : 𝟙_ DModX ⟶ M ⊗ L^∨) :
    ringedSpaceDerivedEvaluationH0ToHom L M' (s ≫ (f ⊗ₘ 𝟙 L^∨)) =
      ringedSpaceDerivedEvaluationH0ToHom L M s ≫ f := by
  simpa using congrFun (ringedSpaceDerivedEvaluationH0ToHom_natural L f).w s

end

end AlgebraicGeometry.RingedSpace
