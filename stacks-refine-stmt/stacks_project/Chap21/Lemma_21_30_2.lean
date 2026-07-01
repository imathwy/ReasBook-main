import Mathlib
import stacks_project.Chap21.«21_30_0_1»
import stacks_project.Chap21.Situation_21_30_1

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory

noncomputable section

universe u v

namespace CategoryTheory.GrothendieckTopology

variable {C : Type u} [Category.{v} C]
variable {τ τ' : GrothendieckTopology C}

variable [∀ X : C, HasInjectiveResolutions (Sheaf (τ'.over X) AddCommGrpCat.{max u v})]
variable [∀ {X Y : C} (f : X ⟶ Y),
  Functor.Additive
    ((Over.map f).sheafPushforwardCocontinuous AddCommGrpCat.{max u v} (τ'.over X) (τ'.over Y))]

/-- The direct-image functor of the localized topology-comparison morphism
`ε_X : Sh(C_τ / X) ⥤ Sh(C_{τ'} / X)` for abelian-group-valued sheaves. -/
noncomputable abbrev localizedTopologyComparisonPushforwardAb
    (hle : τ' ≤ τ) (X : C) :
    Sheaf (τ.over X) AddCommGrpCat.{max u v} ⥤
      Sheaf (τ'.over X) AddCommGrpCat.{max u v} :=
  let _ : Functor.IsContinuous (𝟭 (Over X)) (τ'.over X) (τ.over X) :=
    id_isContinuous_of_le (comparisonOver_le hle X)
  (𝟭 (Over X)).sheafPushforwardContinuous AddCommGrpCat.{max u v} (τ'.over X) (τ.over X)

/-- The localized comparison subcategory `A_X ⊂ Ab(C_τ / X)` obtained by pulling back `A'_X`
along the topology-comparison direct image `ε_{X,*}`. -/
abbrev localizedComparisonObjectProperty
    (hle : τ' ≤ τ)
    (A' : ∀ X : C, ObjectProperty (Sheaf (τ'.over X) AddCommGrpCat.{max u v}))
    (X : C) :
    ObjectProperty (Sheaf (τ.over X) AddCommGrpCat.{max u v}) :=
  (A' X).inverseImage (localizedTopologyComparisonPushforwardAb hle X)

-- Proof sketch: this is exactly the defining `ObjectProperty.inverseImage` predicate for the
-- direct-image functor `ε_{X,*}`, so the statement reduces to unfolding the abbreviation.
/-- Membership in the pulled-back comparison subcategory `A_X` is equivalent to membership of the
direct image under `ε_{X,*}` in `A'_X`. -/
theorem localizedComparisonObjectProperty_iff
    (hle : τ' ≤ τ)
    (A' : ∀ X : C, ObjectProperty (Sheaf (τ'.over X) AddCommGrpCat.{max u v}))
    (X : C)
    (ℱ : Sheaf (τ.over X) AddCommGrpCat.{max u v}) :
    localizedComparisonObjectProperty hle A' X ℱ ↔
      A' X ((localizedTopologyComparisonPushforwardAb hle X).obj ℱ) := sorry

-- Proof sketch: rewrite membership in `A_Y` and `A_X` using
-- `localizedComparisonObjectProperty_iff`. Then apply the commutation of topology comparison with
-- relocalization from the setup and use the inverse-image stability hypothesis on `A'` for the
-- `τ'`-pullback.
/-- Lemma 21.30.2: for the subcategories `A_X ⊂ Ab(C_τ / X)` obtained from `A'_X` by pullback
along the localized topology-comparison morphisms, membership in `A_X` is equivalent to
membership of `ε_{X,*} \mathcal F` in `A'_X`, and inverse image along
`f_\tau^{-1}` sends `A_Y` into `A_X`. -/
theorem localizedComparisonObjectProperty_mem_iff_and_pullback
    (hle : τ' ≤ τ)
    (A' : ∀ X : C, ObjectProperty (Sheaf (τ'.over X) AddCommGrpCat.{max u v}))
    (hinv :
      ∀ ⦃X Y : C⦄ (f : X ⟶ Y) ⦃ℱ : Sheaf (τ'.over Y) AddCommGrpCat.{max u v}⦄,
        A' Y ℱ → A' X ((τ'.overMapPullback AddCommGrpCat.{max u v} f).obj ℱ)) :
    (∀ (X : C) (ℱ : Sheaf (τ.over X) AddCommGrpCat.{max u v}),
      localizedComparisonObjectProperty hle A' X ℱ ↔
        A' X ((localizedTopologyComparisonPushforwardAb hle X).obj ℱ)) ∧
    (∀ ⦃X Y : C⦄ (f : X ⟶ Y) ⦃ℱ : Sheaf (τ.over Y) AddCommGrpCat.{max u v}⦄,
      localizedComparisonObjectProperty hle A' Y ℱ →
        localizedComparisonObjectProperty hle A' X
          ((τ.overMapPullback AddCommGrpCat.{max u v} f).obj ℱ)) := sorry

end CategoryTheory.GrothendieckTopology
