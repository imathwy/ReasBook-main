import StacksProject_2024.Chap21.«21_30_0_1»
import StacksProject_2024.Chap21.Lemma_21_30_2
import StacksProject_2024.Chap21.Situation_21_30_1

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open CategoryTheory.Limits
open scoped CategoryTheory.GrothendieckTopology

noncomputable section

universe u

namespace CategoryTheory.GrothendieckTopology

variable {C : Type u} [Category.{u} C]
variable {τ τ' : GrothendieckTopology C}

/-
Domain-style sampling for Lemma 21.30.3:
- primary domain: localized topology comparison for higher direct images of abelian sheaves on the
  slice sites `C_τ / X` and `C_{τ'} / X`;
- sampled owner declarations:
  `comparisonObjectProperty`,
  `comparisonTopologyPushforwardAb`,
  `CohomologyComparisonSituation.LocalVanishing`,
  `Functor.sheafPushforwardCocontinuousComp'`;
- best owner abstraction:
  `source-facing`: the canonical comparison morphism on higher direct images along `f : X ⟶ Y`;
  `core/canonical`: the slice-site pushforward owners
    `τ.overMapPushforward AddCommGrpCat f`, `τ'.overMapPushforward AddCommGrpCat f`, and the
    topology-comparison pushforward `comparisonTopologyPushforwardAb`;
  `bridge/view`: the acyclicity condition on the pulled-back comparison subcategory `A_X`,
    which is the form of `(V_n)` used to prove the higher-direct-image comparison, together with
    the bridge from the chapter's source-facing local-vanishing condition.

Primitive data are the morphism `f : X ⟶ Y`, the comparison situation `h`, and the pulled-back
comparison subcategories `comparisonObjectProperty hle A' X`. The objectwise acyclicity condition
below is therefore bridge data, not a second root owner for `(V_n)`.
-/

variable (hle : τ' ≤ τ)
variable (P : MorphismProperty C)
variable (A' : ∀ X : C, ObjectProperty (Sheaf (τ'.over X) AddCommGrpCat.{u}))

section Bridge

variable [∀ X : C, HasInjectiveResolutions (Sheaf (τ.over X) AddCommGrpCat.{u})]
variable [∀ X : C, HasInjectiveResolutions (Sheaf (τ'.over X) AddCommGrpCat.{u})]
variable [∀ {X Y : C} (f : X ⟶ Y),
  Functor.Additive
    ((Over.map f).sheafPushforwardCocontinuous AddCommGrpCat.{u}
      (τ.over X) (τ.over Y))]
variable [∀ {X Y : C} (f : X ⟶ Y),
  Functor.Additive
    ((Over.map f).sheafPushforwardCocontinuous AddCommGrpCat.{u}
      (τ'.over X) (τ'.over Y))]
variable [∀ X : C, HasSheafify (τ.over X) AddCommGrpCat.{u}]
variable [∀ X : C, HasExt (Sheaf (τ.over X) AddCommGrpCat.{u})]

-- Proof sketch: evaluate the source-facing local-vanishing condition on the terminal object
-- `Over.mk (𝟙 X)` and the cohomology classes representing the higher derived functors of
-- `ε_{X,*}`. The local vanishing on the terminal object is exactly the acyclicity criterion for
-- the right-derived functors of `comparisonTopologyPushforwardAb hle X`, yielding the bridge from
-- the source-facing `(V_n)` owner to the acyclicity form used in this file.
/- The chapter's source-facing local-vanishing condition `(V_n)` implies the acyclicity of the
localized topology-comparison pushforward `ε_{X,*}` on objects of the pulled-back comparison
subcategory `A_X` in positive degrees up to `n`. -/
theorem comparisonTopologyPushforward_higherDirectImage_isZero_of_localVanishing
    (h : CohomologyComparisonSituation τ τ' P A')
    (n : ℕ)
    (hVn : (V_n) h)
    (X : C)
    (ℱ : Sheaf (τ.over X) AddCommGrpCat.{u})
    (hℱ : A[hle, A']_(X) ℱ)
    (i : ℕ)
    (hi₀ : 0 < i)
    (hi : i ≤ n) :
    IsZero (((comparisonTopologyPushforwardAb hle X).rightDerived i).obj ℱ) := sorry

end Bridge

section HigherDirectImageComparison

variable {X Y : C}

namespace CohomologyComparisonSituation

/-- In Situation `21.30.1`, every morphism `f : X ⟶ Y` with `hf : P f` admits pullbacks along
arbitrary arrows. This is the canonical source-facing bridge from the comparison hypothesis
`hf : P f` to the owner `HasPullbacksAlong f` needed by the localized direct-image functors. -/
instance hasPullbacksAlong
    (h : CohomologyComparisonSituation τ τ' P A')
    (f : X ⟶ Y) (hf : P f) :
    HasPullbacksAlong f := by
  intro W g
  let _ : HasPullback f g := h.hasPullbacks.hasPullback g hf
  change HasPullback g f
  exact hasPullback_symmetry f g

private theorem hasPullbacksAlong'
    (h : CohomologyComparisonSituation τ τ' P A')
    (f : X ⟶ Y) (hf : P f) :
    HasPullbacksAlong f :=
  @hasPullbacksAlong _ _ _ _ _ _ _ _ h f hf

end CohomologyComparisonSituation

open CohomologyComparisonSituation

variable [∀ X : C, HasInjectiveResolutions (Sheaf (τ.over X) AddCommGrpCat.{u})]
variable [∀ X : C, HasInjectiveResolutions (Sheaf (τ'.over X) AddCommGrpCat.{u})]
variable [∀ {X Y : C} (f : X ⟶ Y),
  Functor.Additive
    ((Over.map f).sheafPushforwardCocontinuous AddCommGrpCat.{u}
      (τ.over X) (τ.over Y))]
variable [∀ {X Y : C} (f : X ⟶ Y),
  Functor.Additive
    ((Over.map f).sheafPushforwardCocontinuous AddCommGrpCat.{u}
      (τ'.over X) (τ'.over Y))]
variable [∀ X : C, HasSheafify (τ.over X) AddCommGrpCat.{u}]
variable [∀ X : C, HasExt (Sheaf (τ.over X) AddCommGrpCat.{u})]

/-- The localized direct-image functor `f_{J,*}` attached to a morphism `f : X ⟶ Y` in `P`,
expressed with the source-facing hypothesis `hf : P f` rather than an ambient
`HasPullbacksAlong f` instance. -/
noncomputable abbrev comparisonSituationOverMapPushforward
    {τ τ' : GrothendieckTopology C}
    {P : MorphismProperty C}
    {A' : ∀ X : C, ObjectProperty (Sheaf (τ'.over X) AddCommGrpCat.{u})}
    (h : CohomologyComparisonSituation τ τ' P A')
    (J : GrothendieckTopology C) {X Y : C} (f : X ⟶ Y) (hf : P f) :
    Sheaf (J.over X) AddCommGrpCat.{u} ⥤ Sheaf (J.over Y) AddCommGrpCat.{u} :=
  let _ : HasPullbacksAlong f :=
    show HasPullbacksAlong f from @hasPullbacksAlong' _ _ _ _ _ _ _ _ h f hf
  J.overMapPushforward AddCommGrpCat.{u} f

-- Proof sketch: identify `R ε_{Y,*} R f_{τ,*} ℱ` with `R f_{τ',*} R ε_{X,*} ℱ` via the
-- compatibility isomorphism of `21.30.0.1`. The hypothesis `(V_n)` gives vanishing of the
-- positive-degree `R^p ε_{Y,*}` terms on the relevant objects of `A_Y`, so the relative Leray
-- spectral sequence for `ε_Y` and `f_τ` degenerates on total degree `≤ n`. The surviving
-- `E₂^{0,i}` term yields the desired comparison isomorphism.
/-
Lean realizes the localized direct images `f_{τ,*}` and `f_{τ',*}` via the canonical Chapter
`21.30.0.1` owner `J.overMapPushforward AddCommGrpCat f`. The bridge
`comparisonSituationOverMapPushforward` packages the canonical
`HasPullbacksAlong f` owner coming from `hf : P f`, so the statement keeps only the source-facing
hypothesis `hf`.
 -/
/-- Lemma 21.30.3: in Situation 21.30.1, assuming `(V_n)`, for a morphism `f : X ⟶ Y` in `P`
and `ℱ ∈ A_X`, the higher direct images of `ℱ` along `f` commute with the topology-comparison
direct image `ε_*` in degrees `i ≤ n` via the canonical comparison isomorphism. -/
@[stacks 0EZA]
theorem higherDirectImage_localizedTopologyComparison_isomorphic
    (h : CohomologyComparisonSituation τ τ' P A')
    (n : ℕ)
    (hVn : (V_n) h)
    (f : X ⟶ Y) (hf : P f)
    (ℱ : Sheaf (τ.over X) AddCommGrpCat.{u})
    (hℱ : A[hle, A']_(X) ℱ)
    (i : ℕ) (hi : i ≤ n) :
    IsIsomorphic
      ((((comparisonSituationOverMapPushforward h τ' f hf).rightDerived i).obj
          ((comparisonTopologyPushforwardAb hle X).obj ℱ)))
      ((comparisonTopologyPushforwardAb hle Y).obj
        (((comparisonSituationOverMapPushforward h τ f hf).rightDerived i).obj ℱ)) := by
  sorry

end HigherDirectImageComparison

end CategoryTheory.GrothendieckTopology
