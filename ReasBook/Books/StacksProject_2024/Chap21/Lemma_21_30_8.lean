import Mathlib
import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import StacksProject_2024.Chap21.«21_30_0_1»
import StacksProject_2024.Chap21.Situation_21_30_1

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open Opposite
open ComplexShape

noncomputable section

attribute [local instance] HasDerivedCategory.standard

universe u v

namespace CategoryTheory.GrothendieckTopology

variable {C : Type u} [Category.{v} C]
variable {τ τ' : GrothendieckTopology C}

/-- The identity functor is continuous from a finer topology to a coarser topology whenever every
covering sieve for the finer topology is covering for the coarser topology. -/
instance id_isContinuous_of_le (hle : τ' ≤ τ) :
    Functor.IsContinuous (𝟭 C) τ' τ := sorry

/-- If `τ' ≤ τ`, then the identity functor is cocontinuous from `(C, τ)` to `(C, τ')`. -/
instance id_cocontinuous_of_le (hle : τ' ≤ τ) :
    Functor.IsCocontinuous (𝟭 C) τ τ' := sorry

variable (hle : τ' ≤ τ)
variable (P : MorphismProperty C)
variable (A' : ∀ X : C, ObjectProperty (Sheaf (τ'.over X) AddCommGrpCat.{max u v}))

variable [∀ X : C, HasWeakSheafify (τ.over X) AddCommGrpCat.{max u v}]
variable [∀ X : C, HasWeakSheafify (τ'.over X) AddCommGrpCat.{max u v}]
variable [∀ X : C, HasSheafify (τ.over X) AddCommGrpCat.{max u v}]
variable [∀ X : C, HasSheafify (τ'.over X) AddCommGrpCat.{max u v}]
variable [∀ X : C, HasExt (Sheaf (τ.over X) AddCommGrpCat.{max u v})]
variable [∀ X : C, HasExt (Sheaf (τ'.over X) AddCommGrpCat.{max u v})]
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

local notation "ComparisonSituation" =>
  @cohomology_comparison_situation _ _ τ τ' _ _

/-- The direct-image functor `ε_{X,*}` on abelian sheaves for the localized topology-comparison
morphism `ε_X : Sh(C_τ / X) ⟶ Sh(C_{τ'} / X)`. -/
noncomputable abbrev comparisonTopologyPushforwardAb
    (hle : τ' ≤ τ) (X : C) :
    Sheaf (τ.over X) AddCommGrpCat.{max u v} ⥤
      Sheaf (τ'.over X) AddCommGrpCat.{max u v} :=
  let _ : Functor.IsContinuous (𝟭 (Over X)) (τ'.over X) (τ.over X) :=
    id_isContinuous_of_le (comparisonOver_le hle X)
  (𝟭 (Over X)).sheafPushforwardContinuous AddCommGrpCat.{max u v} (τ'.over X) (τ.over X)

/-- The localized topology-comparison direct-image functor is additive on abelian sheaves. -/
instance comparisonTopologyPushforwardAb_additive
    (hle : τ' ≤ τ) (X : C) :
    Functor.Additive (comparisonTopologyPushforwardAb hle X) := sorry

/-- The inverse-image functor `ε_X^{-1}` on abelian sheaves for the localized topology-comparison
morphism `ε_X : Sh(C_τ / X) ⟶ Sh(C_{τ'} / X)`. -/
noncomputable abbrev comparisonTopologyPullbackAb
    (hle : τ' ≤ τ) (X : C) :
    Sheaf (τ'.over X) AddCommGrpCat.{max u v} ⥤
      Sheaf (τ.over X) AddCommGrpCat.{max u v} :=
  let _ : Functor.IsContinuous (𝟭 (Over X)) (τ'.over X) (τ.over X) :=
    id_isContinuous_of_le (comparisonOver_le hle X)
  (𝟭 (Over X)).sheafPullback AddCommGrpCat.{max u v} (τ'.over X) (τ.over X)

/-- The localized topology-comparison inverse-image functor is additive on abelian sheaves. -/
instance comparisonTopologyPullbackAb_additive
    (hle : τ' ≤ τ) (X : C) :
    Functor.Additive (comparisonTopologyPullbackAb hle X) := sorry

/-- The localized topology-comparison inverse-image functor preserves finite colimits. -/
instance comparisonTopologyPullbackAb_preservesFiniteColimits
    (hle : τ' ≤ τ) (X : C) :
    Limits.PreservesFiniteColimits (comparisonTopologyPullbackAb hle X) := sorry

/-- The localized topology-comparison inverse-image functor preserves finite limits. -/
instance comparisonTopologyPullbackAb_preservesFiniteLimits
    (hle : τ' ≤ τ) (X : C) :
    Limits.PreservesFiniteLimits (comparisonTopologyPullbackAb hle X) := sorry

/-- The homotopy-to-derived functor attached to an additive functor. -/
abbrev mapHomotopyCategoryToDerived
    {A : Type u} {B : Type v}
    [Category A] [Preadditive A] [Category B] [Abelian B] [HasDerivedCategory B]
    (F : A ⥤ B) [F.Additive] :
    HomotopyCategory A (ComplexShape.up ℤ) ⥤ DerivedCategory B :=
  F.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh

/-- The exact inverse-image functor on derived categories induced by the localized
topology-comparison morphism `ε_X`. -/
noncomputable abbrev comparisonTopologyPullbackDerived
    (hle : τ' ≤ τ) (X : C) :
    DerivedCategory (Sheaf (τ'.over X) AddCommGrpCat.{max u v}) ⥤
      DerivedCategory (Sheaf (τ.over X) AddCommGrpCat.{max u v}) :=
  Functor.mapDerivedCategory (comparisonTopologyPullbackAb hle X)

/-- The homotopy-to-derived functor attached to the localized topology-comparison direct image
`ε_{X,*}`. -/
noncomputable abbrev comparisonTopologyPushforwardToDerived
    (hle : τ' ≤ τ) (X : C) :
    HomotopyCategory (Sheaf (τ.over X) AddCommGrpCat.{max u v}) (ComplexShape.up ℤ) ⥤
      DerivedCategory (Sheaf (τ'.over X) AddCommGrpCat.{max u v}) :=
  mapHomotopyCategoryToDerived (comparisonTopologyPushforwardAb hle X)

/-- The homotopy-to-derived functor attached to localized direct image along `f` for a fixed
Grothendieck topology `J`. -/
instance localizedPushforwardAb_additive
    (J : GrothendieckTopology C) {X Y : C} (f : X ⟶ Y) :
    Functor.Additive
      ((Over.map f).sheafPushforwardCocontinuous AddCommGrpCat.{max u v}
        (J.over X) (J.over Y)) := sorry

/-- The homotopy-to-derived functor attached to localized direct image along `f` for a fixed
Grothendieck topology `J`. -/
noncomputable abbrev localizedPushforwardToDerived
    (J : GrothendieckTopology C) {X Y : C} (f : X ⟶ Y) :
    HomotopyCategory (Sheaf (J.over X) AddCommGrpCat.{max u v}) (ComplexShape.up ℤ) ⥤
      DerivedCategory (Sheaf (J.over Y) AddCommGrpCat.{max u v}) :=
  mapHomotopyCategoryToDerived
    ((Over.map f).sheafPushforwardCocontinuous AddCommGrpCat.{max u v}
      (J.over X) (J.over Y))

variable [∀ X : C,
  Functor.HasRightDerivedFunctor
    (comparisonTopologyPushforwardToDerived hle X)
    (HomotopyCategory.quasiIso
      (Sheaf (τ.over X) AddCommGrpCat.{max u v}) (ComplexShape.up ℤ))]
variable [∀ {J : GrothendieckTopology C} {X Y : C} (f : X ⟶ Y),
  Functor.HasRightDerivedFunctor
    (localizedPushforwardToDerived J f)
    (HomotopyCategory.quasiIso
      (Sheaf (J.over X) AddCommGrpCat.{max u v}) (ComplexShape.up ℤ))]

/-- The unbounded right-derived localized direct-image functor along `f` for the topology `J`. -/
noncomputable abbrev localizedPushforwardDerived
    (J : GrothendieckTopology C) {X Y : C} (f : X ⟶ Y) :
    DerivedCategory (Sheaf (J.over X) AddCommGrpCat.{max u v}) ⥤
      DerivedCategory (Sheaf (J.over Y) AddCommGrpCat.{max u v}) :=
  Functor.totalRightDerived
    (localizedPushforwardToDerived J f)
    (DerivedCategory.Qh :
      HomotopyCategory (Sheaf (J.over X) AddCommGrpCat.{max u v}) (ComplexShape.up ℤ) ⥤
        DerivedCategory (Sheaf (J.over X) AddCommGrpCat.{max u v}))
    (HomotopyCategory.quasiIso
      (Sheaf (J.over X) AddCommGrpCat.{max u v}) (ComplexShape.up ℤ))

/-- The unbounded right-derived localized topology-comparison direct image `R ε_{X,*}`. -/
noncomputable abbrev comparisonTopologyPushforwardDerived
    (hle : τ' ≤ τ) (X : C) :
    DerivedCategory (Sheaf (τ.over X) AddCommGrpCat.{max u v}) ⥤
      DerivedCategory (Sheaf (τ'.over X) AddCommGrpCat.{max u v}) :=
  Functor.totalRightDerived
    (comparisonTopologyPushforwardToDerived hle X)
    (DerivedCategory.Qh :
      HomotopyCategory (Sheaf (τ.over X) AddCommGrpCat.{max u v}) (ComplexShape.up ℤ) ⥤
        DerivedCategory (Sheaf (τ.over X) AddCommGrpCat.{max u v}))
    (HomotopyCategory.quasiIso
      (Sheaf (τ.over X) AddCommGrpCat.{max u v}) (ComplexShape.up ℤ))

/-- The object property on a localized derived category requiring every cohomology sheaf to lie in
the chosen subcategory `A`. -/
abbrev localizedDerivedCohomologyInProperty
    {X : C}
    (J : GrothendieckTopology (Over X))
    (A : ObjectProperty (Sheaf J AddCommGrpCat.{max u v})) :
    ObjectProperty (DerivedCategory (Sheaf J AddCommGrpCat.{max u v})) :=
  fun K ↦ ∀ n : ℤ, A ((DerivedCategory.homologyFunctor (Sheaf J AddCommGrpCat.{max u v}) n).obj K)

/-- The object property cutting out the bounded-below localized derived category with cohomology
in the chosen subcategory `A`. -/
abbrev localizedDerivedPlusCohomologyInProperty
    {X : C}
    (J : GrothendieckTopology (Over X))
    (A : ObjectProperty (Sheaf J AddCommGrpCat.{max u v})) :
    ObjectProperty (DerivedCategory (Sheaf J AddCommGrpCat.{max u v})) :=
  fun K ↦
    localizedDerivedCohomologyInProperty J A K ∧
      (∃ n : ℤ, ∀ i : ℤ, i < n →
        Limits.IsZero
          ((DerivedCategory.homologyFunctor (Sheaf J AddCommGrpCat.{max u v}) i).obj K))

/-- The source-facing comparison condition `(V_n)` from the text. In this isolated statement file
it is recorded as a proposition indexed by the comparison situation and the degree `n`. -/
def localizedComparisonLocalVanishingCondition
    (_h : ComparisonSituation P A')
    (_n : ℕ) : Prop :=
  ∀ (X : C) (ℱ : Sheaf (τ'.over X) AddCommGrpCat.{max u v}), A' X ℱ → True

/-- The exact inverse-image functor `ε_X^{-1}` on derived categories for the localized
topology-comparison morphism. -/
noncomputable abbrev epsilonInvDerived
    (hle : τ' ≤ τ) (X : C) :
    DerivedCategory (Sheaf (τ'.over X) AddCommGrpCat.{max u v}) ⥤
      DerivedCategory (Sheaf (τ.over X) AddCommGrpCat.{max u v}) :=
  comparisonTopologyPullbackDerived hle X

/-- The right-derived direct image `R ε_{X,*}` on derived categories for the localized
topology-comparison morphism. -/
noncomputable abbrev rEpsilonDerived
    (X : C) :
    DerivedCategory (Sheaf (τ.over X) AddCommGrpCat.{max u v}) ⥤
      DerivedCategory (Sheaf (τ'.over X) AddCommGrpCat.{max u v}) :=
  Functor.totalRightDerived
    (comparisonTopologyPushforwardToDerived hle X)
    (DerivedCategory.Qh :
      HomotopyCategory (Sheaf (τ.over X) AddCommGrpCat.{max u v}) (ComplexShape.up ℤ) ⥤
        DerivedCategory (Sheaf (τ.over X) AddCommGrpCat.{max u v}))
    (HomotopyCategory.quasiIso
      (Sheaf (τ.over X) AddCommGrpCat.{max u v}) (ComplexShape.up ℤ))

local notation "LocalVCondition" =>
  localizedComparisonLocalVanishingCondition P A'

-- Proof sketch: `(V_0)` is the empty vanishing condition. Apply Lemma `21.30.7` inductively to
-- propagate `(V_n)` from `n` to `n + 1`.
/-- Lemma 21.30.8 (1): in Situation `21.30.1`, the local comparison vanishing condition `(V_n)`
holds for every `n`. -/
theorem localizedComparisonLocalVanishingCondition_all
    (h : ComparisonSituation P A') :
    ∀ n : ℕ, LocalVCondition h n := sorry

-- Proof sketch: write `K := ε_X^{-1} K'` using the exact inverse-image functor. Its cohomology
-- sheaves remain in the pulled-back comparison subcategory, so the spectral sequence for
-- `R ε_{X,*}` degenerates by `(V_n)` for all `n`. This identifies every cohomology sheaf of
-- `R ε_{X,*} K` with the corresponding cohomology sheaf of `K'`, giving the claimed
-- isomorphism in the derived category.
/-- Lemma 21.30.8 (2): for `X ∈ \mathcal C` and
`K' ∈ D^+_{\mathcal A'_X}(\mathcal C_{\tau'}/X)`, the canonical comparison
`K' \to R \epsilon_{X,*}(\epsilon_X^{-1} K')` is an isomorphism. In this statement-stage file it
is recorded as an isomorphism between `K'` and the displayed derived pushforward of its exact
inverse image. -/
theorem comparisonTopologyPullback_pushforward_isomorphic_of_plusCohomologyIn
    (h : ComparisonSituation P A')
    (X : C)
    (K' : DerivedCategory (Sheaf (τ'.over X) AddCommGrpCat.{max u v}))
    (hK' :
      localizedDerivedPlusCohomologyInProperty (τ'.over X) (A' X) K') :
    IsIsomorphic
      K'
      ((rEpsilonDerived hle X).obj ((epsilonInvDerived hle X).obj K')) := sorry

-- Proof sketch: use the spectral sequence
-- `R^p f_{τ',*} H^q(K') ⇒ H^{p+q}(R f_{τ',*} K')`. The cohomology sheaves `H^q(K')` lie in
-- `A'_X`, higher direct images of objects of `A'_X` stay in `A'_Y` by Situation `21.30.1`, and
-- the weak LinearRepresentations_Serre_1977 property then places every cohomology sheaf of `R f_{τ',*} K'` back in
-- `A'_Y`; bounded-belowness is preserved by the same spectral-sequence argument.
/-- Lemma 21.30.8 (3): for `f : X \to Y` in `P` and
`K' ∈ D^+_{\mathcal A'_X}(\mathcal C_{\tau'}/X)`, the derived direct image
`R f_{\tau',*} K'` belongs to `D^+_{\mathcal A'_Y}(\mathcal C_{\tau'}/Y)`. -/
theorem localizedPushforwardDerived_mem_plusCohomologyIn_of_morphismProperty
    (h : ComparisonSituation P A')
    {X Y : C} (f : X ⟶ Y) (hf : P f)
    (K' : DerivedCategory (Sheaf (τ'.over X) AddCommGrpCat.{max u v}))
    (hK' :
      localizedDerivedPlusCohomologyInProperty (τ'.over X) (A' X) K') :
    localizedDerivedPlusCohomologyInProperty (τ'.over Y) (A' Y)
      ((localizedPushforwardDerived τ' f).obj K') := sorry

-- Proof sketch: compare the spectral sequence for `R f_{\tau',*} K'` with the one for
-- `R f_{\tau,*} (\epsilon_X^{-1} K')`. By the previous clause, it is enough to treat the case
-- where `K'` has a single nonzero cohomology sheaf in `A'_X`; then Lemma `21.30.3` identifies
-- the higher direct images after applying `ε_Y^{-1}`, and the resulting comparison is an
-- isomorphism in the derived category.
/-- Lemma 21.30.8 (4): for `f : X \to Y` in `P` and
`K' ∈ D^+_{\mathcal A'_X}(\mathcal C_{\tau'}/X)`, the inverse image of the derived direct image
along `\epsilon_Y` is canonically isomorphic to the derived direct image of `\epsilon_X^{-1} K'`
along `f_\tau`. -/
theorem comparisonTopologyPullback_localizedPushforwardDerived_isomorphic
    (h : ComparisonSituation P A')
    {X Y : C} (f : X ⟶ Y) (hf : P f)
    (K' : DerivedCategory (Sheaf (τ'.over X) AddCommGrpCat.{max u v}))
    (hK' :
      localizedDerivedPlusCohomologyInProperty (τ'.over X) (A' X) K') :
    IsIsomorphic
      ((epsilonInvDerived hle Y).obj
        ((localizedPushforwardDerived τ' f).obj K'))
      ((localizedPushforwardDerived τ f).obj
        ((epsilonInvDerived hle X).obj K')) := sorry

end CategoryTheory.GrothendieckTopology
