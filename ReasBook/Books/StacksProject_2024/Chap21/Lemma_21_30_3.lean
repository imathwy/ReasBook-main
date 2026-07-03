import Mathlib
import StacksProject_2024.Chap21.«21_30_0_1»
import StacksProject_2024.Chap21.Situation_21_30_1

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory

noncomputable section

universe u v

namespace CategoryTheory.GrothendieckTopology

variable {C : Type u} [Category.{v} C]
variable {τ τ' : GrothendieckTopology C}

variable (hle : τ' ≤ τ)
variable (P : MorphismProperty C)
variable (A' : ∀ X : C, ObjectProperty (Sheaf (τ'.over X) AddCommGrpCat.{max u v}))

variable [∀ X : C, HasInjectiveResolutions (Sheaf (τ.over X) AddCommGrpCat.{max u v})]
variable [∀ X : C, HasInjectiveResolutions (Sheaf (τ'.over X) AddCommGrpCat.{max u v})]
variable [∀ {X Y : C} (f : X ⟶ Y),
  Functor.Additive
    ((Over.map f).sheafPushforwardCocontinuous AddCommGrpCat.{max u v}
      (τ.over X) (τ.over Y))]
variable [∀ {X Y : C} (f : X ⟶ Y),
  Functor.Additive
    ((Over.map f).sheafPushforwardCocontinuous AddCommGrpCat.{max u v}
      (τ'.over X) (τ'.over Y))]

/-- The direct-image functor of the localized topology-comparison morphism
`ε_X : Sh(C_τ / X) ⥤ Sh(C_{τ'} / X)` for abelian-group-valued sheaves. -/
noncomputable abbrev comparisonTopologyPushforwardAb
    (hle : τ' ≤ τ) (X : C) :
    Sheaf (τ.over X) AddCommGrpCat.{max u v} ⥤
      Sheaf (τ'.over X) AddCommGrpCat.{max u v} :=
  let _ : Functor.IsContinuous (𝟭 (Over X)) (τ'.over X) (τ.over X) :=
    id_isContinuous_of_le (comparisonOver_le hle X)
  (𝟭 (Over X)).sheafPushforwardContinuous AddCommGrpCat.{max u v} (τ'.over X) (τ.over X)

-- Proof sketch: `comparisonTopologyPushforwardAb hle X` is a sheaf pushforward functor induced by
-- a continuous identity functor between abelian sheaf categories, hence it preserves the additive
-- structure objectwise.
/-- The localized topology-comparison pushforward on abelian sheaves is additive. -/
instance comparisonTopologyPushforwardAb_additive
    (hle : τ' ≤ τ) (X : C) :
    Functor.Additive (comparisonTopologyPushforwardAb hle X) := sorry

/-- The localized comparison subcategory `A_X ⊂ Ab(C_τ / X)` obtained by pulling back `A'_X`
along the topology-comparison direct image `ε_{X,*}`. -/
abbrev comparisonObjectProperty
    (hle : τ' ≤ τ)
    (A' : ∀ X : C, ObjectProperty (Sheaf (τ'.over X) AddCommGrpCat.{max u v}))
    (X : C) :
    ObjectProperty (Sheaf (τ.over X) AddCommGrpCat.{max u v}) :=
  (A' X).inverseImage (comparisonTopologyPushforwardAb hle X)

-- Proof sketch: unfold `comparisonObjectProperty`; it is exactly the inverse-image predicate for
-- the direct-image functor `ε_{X,*}`.
/-- Membership in the pulled-back comparison subcategory `A_X` is equivalent to membership of the
direct image under `ε_{X,*}` in `A'_X`. -/
theorem comparisonObjectProperty_iff
    (hle : τ' ≤ τ)
    (A' : ∀ X : C, ObjectProperty (Sheaf (τ'.over X) AddCommGrpCat.{max u v}))
    (X : C)
    (ℱ : Sheaf (τ.over X) AddCommGrpCat.{max u v}) :
    comparisonObjectProperty hle A' X ℱ ↔
      A' X ((comparisonTopologyPushforwardAb hle X).obj ℱ) := sorry

/-- The comparison hypothesis `(V_n)` for the topology morphisms `ε_X` says that every object of
the pulled-back comparison subcategory `A_X` is `ε_{X,*}`-acyclic in positive degrees up to `n`.
-/
def localizedTopologyComparisonConditionV
    (hle : τ' ≤ τ)
    (A' : ∀ X : C, ObjectProperty (Sheaf (τ'.over X) AddCommGrpCat.{max u v}))
    (n : ℕ) : Prop :=
  ∀ (X : C) (ℱ : Sheaf (τ.over X) AddCommGrpCat.{max u v}),
    comparisonObjectProperty hle A' X ℱ →
      ∀ i : ℕ, 0 < i → i ≤ n →
        CategoryTheory.Limits.IsZero
          (((comparisonTopologyPushforwardAb hle X).rightDerived i).obj ℱ)

-- Proof sketch: identify `R ε_{Y,*} R f_{τ,*} ℱ` with `R f_{τ',*} R ε_{X,*} ℱ` via the
-- compatibility isomorphism of `21.30.0.1`. The hypothesis `(V_n)` gives vanishing of the
-- positive-degree `R^p ε_{Y,*}` terms on the relevant objects of `A_Y`, so the relative Leray
-- spectral sequence for `ε_Y` and `f_τ` degenerates on total degree `≤ n`. The surviving
-- `E₂^{0,i}` term yields the desired comparison isomorphism.
/-- Lemma 21.30.3: in Situation 21.30.1, assuming `(V_n)`, for a morphism `f : X ⟶ Y` in `P` and
`ℱ ∈ A_X`, the higher direct images of `ℱ` along `f` commute with the topology-comparison direct
image `ε_*` in degrees `i ≤ n`, up to canonical isomorphism. -/
theorem higherDirectImage_localizedTopologyComparison_iso
    (h : CategoryTheory.GrothendieckTopology.cohomology_comparison_situation τ τ' P A')
    (n : ℕ)
    (hVn : localizedTopologyComparisonConditionV hle A' n)
    {X Y : C} (f : X ⟶ Y) (hf : P f)
    (ℱ : Sheaf (τ.over X) AddCommGrpCat.{max u v})
    (hℱ : comparisonObjectProperty hle A' X ℱ)
    (i : ℕ) (hi : i ≤ n) :
    IsIsomorphic
      ((((Over.map f).sheafPushforwardCocontinuous AddCommGrpCat.{max u v}
          (τ'.over X) (τ'.over Y)).rightDerived i).obj
        ((comparisonTopologyPushforwardAb hle X).obj ℱ))
      ((comparisonTopologyPushforwardAb hle Y).obj
        ((((Over.map f).sheafPushforwardCocontinuous AddCommGrpCat.{max u v}
            (τ.over X) (τ.over Y)).rightDerived i).obj ℱ)) := sorry

end CategoryTheory.GrothendieckTopology
