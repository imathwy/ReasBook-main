import Mathlib
import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Lemma_21_30_2 (from Chap21) -/
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

/-! ### Lemma_21_30_3 (from Chap21) -/
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

/-! ### Lemma_21_30_4 (from Chap21) -/
open CategoryTheory
open CategoryTheory.Limits

noncomputable section

universe u v

attribute [local instance] HasDerivedCategory.standard

namespace CategoryTheory.GrothendieckTopology

variable {C : Type u} [Category.{v} C]
variable {τ τ' : GrothendieckTopology C}

/-- The degree-`n` hypercohomology object of a derived abelian sheaf on a localized site,
computed by a chosen derived global-sections functor. -/
abbrev localizedSiteHypercohomology
    {X : C} {J : GrothendieckTopology (Over X)}
    (RGamma : DerivedCategory (Sheaf J AddCommGrpCat.{max u v}) ⥤
      DerivedCategory AddCommGrpCat.{max u v})
    (L : DerivedCategory (Sheaf J AddCommGrpCat.{max u v})) (n : ℕ) :
    AddCommGrpCat.{max u v} :=
  (DerivedCategory.homologyFunctor AddCommGrpCat.{max u v} (n : ℤ)).obj (RGamma.obj L)

/-- A derived object on `(C_{τ'}/X)` has comparison cohomology in range `≤ n` if it has no
negative cohomology and each cohomology sheaf `H^i(L)` for `0 ≤ i ≤ n` lies in the chosen
subcategory `A'_X`. -/
def localizedComparisonCohomologyInRange
    (A' : ∀ X : C, ObjectProperty (Sheaf (τ'.over X) AddCommGrpCat.{max u v}))
    (X : C) (L : DerivedCategory (Sheaf (τ'.over X) AddCommGrpCat.{max u v})) (n : ℕ) : Prop :=
  (∀ i : ℤ, i < 0 →
      IsZero
        ((DerivedCategory.homologyFunctor
          (Sheaf (τ'.over X) AddCommGrpCat.{max u v}) i).obj L)) ∧
    ∀ i : ℕ, i ≤ n →
      A' X
        ((DerivedCategory.homologyFunctor
          (Sheaf (τ'.over X) AddCommGrpCat.{max u v}) (i : ℤ)).obj L)

/-- The degree-zero comparison condition says that for every `F ∈ A'_X`, the degree-zero
cohomology sheaf of `R ε_{X,*}(ε_X^{-1} F[0])` is canonically identified with `F`. -/
def localizedTopologyComparisonDegreeZeroCondition
    (A' : ∀ X : C, ObjectProperty (Sheaf (τ'.over X) AddCommGrpCat.{max u v}))
    (epsilonInverseImageDerived : ∀ X : C,
      DerivedCategory (Sheaf (τ'.over X) AddCommGrpCat.{max u v}) ⥤
        DerivedCategory (Sheaf (τ.over X) AddCommGrpCat.{max u v}))
    (epsilonPushforwardDerived : ∀ X : C,
      DerivedCategory (Sheaf (τ.over X) AddCommGrpCat.{max u v}) ⥤
        DerivedCategory (Sheaf (τ'.over X) AddCommGrpCat.{max u v})) : Prop :=
  ∀ (X : C) (F : Sheaf (τ'.over X) AddCommGrpCat.{max u v}),
    A' X F →
      IsIsomorphic
        ((DerivedCategory.homologyFunctor
          (Sheaf (τ'.over X) AddCommGrpCat.{max u v}) (0 : ℤ)).obj
          ((epsilonPushforwardDerived X).obj
            ((epsilonInverseImageDerived X).obj
              ((DerivedCategory.singleFunctor
                (Sheaf (τ'.over X) AddCommGrpCat.{max u v}) (0 : ℤ)).obj F))))
        F

/-- The vanishing condition `(V_n)` for the localized comparison says that for every `F ∈ A'_X`,
the higher cohomology sheaves `R^p ε_{X,*}(ε_X^{-1} F)` vanish for `1 ≤ p ≤ n`, here encoded on
the degree-`p` cohomology of `R ε_{X,*}(ε_X^{-1} F[0])`. -/
def localizedTopologyComparisonConditionV
    (A' : ∀ X : C, ObjectProperty (Sheaf (τ'.over X) AddCommGrpCat.{max u v}))
    (epsilonInverseImageDerived : ∀ X : C,
      DerivedCategory (Sheaf (τ'.over X) AddCommGrpCat.{max u v}) ⥤
        DerivedCategory (Sheaf (τ.over X) AddCommGrpCat.{max u v}))
    (epsilonPushforwardDerived : ∀ X : C,
      DerivedCategory (Sheaf (τ.over X) AddCommGrpCat.{max u v}) ⥤
        DerivedCategory (Sheaf (τ'.over X) AddCommGrpCat.{max u v}))
    (n : ℕ) : Prop :=
  ∀ (X : C) (F : Sheaf (τ'.over X) AddCommGrpCat.{max u v}) (p : ℕ),
    A' X F → 0 < p → p ≤ n →
      IsZero
        ((DerivedCategory.homologyFunctor
          (Sheaf (τ'.over X) AddCommGrpCat.{max u v}) (p : ℤ)).obj
          ((epsilonPushforwardDerived X).obj
            ((epsilonInverseImageDerived X).obj
              ((DerivedCategory.singleFunctor
                (Sheaf (τ'.over X) AddCommGrpCat.{max u v}) (0 : ℤ)).obj F))))

-- Proof sketch: apply the Grothendieck spectral sequence for the composite
-- `RΓ_{τ'/X} ∘ R ε_{X,*}` to the object `ε_X^{-1} L`. The negative cohomology vanishing and the
-- range hypothesis on the cohomology sheaves of `L` reduce the `E₂`-page in total degree `n` to
-- the column `p = 0`, using the degree-zero comparison condition for `A'_X` together with the
-- vanishing condition `(V_n)`. The edge-map comparison then identifies `H^n_{τ'}(X, L)` with
-- `H^n_τ(X, ε_X^{-1}L)`.
/-- Lemma 21.30.4: assuming the degree-zero comparison on the chosen subcategories `A'_X` and the
vanishing condition `(V_n)`, if `L ∈ D(\mathcal C_{τ'}/X)` has `H^i(L) = 0` for `i < 0` and
`H^i(L) ∈ A'_X` for `0 ≤ i ≤ n`, then the degree-`n` hypercohomology of `L` over `τ'` is
canonically isomorphic to the degree-`n` hypercohomology of `ε_X^{-1}L` over `τ`. -/
theorem hypercohomology_comparison_isomorphic_of_conditionV
    (n : ℕ)
    (A' : ∀ X : C, ObjectProperty (Sheaf (τ'.over X) AddCommGrpCat.{max u v}))
    (epsilonInverseImageDerived : ∀ X : C,
      DerivedCategory (Sheaf (τ'.over X) AddCommGrpCat.{max u v}) ⥤
        DerivedCategory (Sheaf (τ.over X) AddCommGrpCat.{max u v}))
    (epsilonPushforwardDerived : ∀ X : C,
      DerivedCategory (Sheaf (τ.over X) AddCommGrpCat.{max u v}) ⥤
        DerivedCategory (Sheaf (τ'.over X) AddCommGrpCat.{max u v}))
    (RGammaTau : ∀ X : C,
      DerivedCategory (Sheaf (τ.over X) AddCommGrpCat.{max u v}) ⥤
        DerivedCategory AddCommGrpCat.{max u v})
    (RGammaTau' : ∀ X : C,
      DerivedCategory (Sheaf (τ'.over X) AddCommGrpCat.{max u v}) ⥤
        DerivedCategory AddCommGrpCat.{max u v})
    (hDegreeZero :
      localizedTopologyComparisonDegreeZeroCondition A' epsilonInverseImageDerived
        epsilonPushforwardDerived)
    (hVn :
      localizedTopologyComparisonConditionV A' epsilonInverseImageDerived
        epsilonPushforwardDerived n)
    (X : C)
    (L : DerivedCategory (Sheaf (τ'.over X) AddCommGrpCat.{max u v}))
    (hL : localizedComparisonCohomologyInRange A' X L n) :
    IsIsomorphic
      (localizedSiteHypercohomology (RGammaTau' X) L n)
      (localizedSiteHypercohomology (RGammaTau X)
        ((epsilonInverseImageDerived X).obj L) n) := sorry

end CategoryTheory.GrothendieckTopology

/-! ### Lemma_21_30_5 (from Chap21) -/
open CategoryTheory Opposite
open CategoryTheory.GrothendieckTopology

noncomputable section

universe u

namespace CategoryTheory.GrothendieckTopology

variable {C : Type u} [Category.{u} C]
variable {τ τ' : GrothendieckTopology C}

/-- The terminal object of the localized category `Over X`. -/
abbrev terminalOver (X : C) : Over X :=
  Over.mk (𝟙 X)

/-- The direct-image functor of the localized topology-comparison morphism
`ε_X : Sh(C_τ / X) ⥤ Sh(C_{τ'} / X)` for abelian-group-valued sheaves. -/
noncomputable abbrev localizedTopologyComparisonPushforwardAb'
    (hle : τ' ≤ τ) (X : C) :
    Sheaf (τ.over X) AddCommGrpCat ⥤ Sheaf (τ'.over X) AddCommGrpCat :=
  let _ : Functor.IsContinuous (𝟭 (Over X)) (τ'.over X) (τ.over X) :=
    id_isContinuous_of_le (comparisonOver_le hle X)
  (𝟭 (Over X)).sheafPushforwardContinuous AddCommGrpCat (τ'.over X) (τ.over X)

/-- The localized topology-comparison pushforward is additive on abelian sheaves. -/
instance localizedTopologyComparisonPushforwardAb'_additive
    (hle : τ' ≤ τ) (X : C) :
    Functor.Additive (localizedTopologyComparisonPushforwardAb' hle X) := sorry

/-- The objectwise degree-`n` cohomology of a sheaf on a localized site, evaluated at the
terminal object of `Over X`. -/
abbrev terminalOverCohomology {X : C} {J : GrothendieckTopology (Over X)}
    [HasSheafify J AddCommGrpCat]
    [HasExt (Sheaf J AddCommGrpCat)]
    (ℱ : Sheaf J AddCommGrpCat) (n : ℕ) : AddCommGrpCat :=
  ℱ.H' n (terminalOver X)

/-- The `q`-th higher direct image of an abelian sheaf on `(C_τ/X)` along the localized
topology-comparison morphism `ε_X`. -/
abbrev localizedComparisonHigherDirectImage
    (hle : τ' ≤ τ) (X : C)
    [HasInjectiveResolutions (Sheaf (τ.over X) AddCommGrpCat)]
    (ℱ : Sheaf (τ.over X) AddCommGrpCat) (q : ℕ) :
    Sheaf (τ'.over X) AddCommGrpCat :=
  ((localizedTopologyComparisonPushforwardAb' hle X).rightDerived q).obj ℱ

/-- The vanishing hypothesis `(V_n)` at a fixed object `X`: positive-degree objectwise cohomology
of the higher direct images `R^q ε_{X,*} \mathcal F` vanishes on the terminal object of
`Over X` for `1 ≤ q ≤ n`. -/
abbrev localizedComparisonVCondition
    (hle : τ' ≤ τ) (X : C)
    [HasSheafify (τ'.over X) AddCommGrpCat]
    [HasExt (Sheaf (τ'.over X) AddCommGrpCat)]
    [HasInjectiveResolutions (Sheaf (τ.over X) AddCommGrpCat)]
    (ℱ : Sheaf (τ.over X) AddCommGrpCat) (n : ℕ) : Prop :=
  ∀ q p : ℕ, 1 ≤ q → q ≤ n → 0 < p →
    Limits.IsZero
      (terminalOverCohomology (localizedComparisonHigherDirectImage hle X ℱ q) p)

/-- A degree-`n + 1` cohomology class on `(C_τ/X)` becomes trivial on a `τ'`-covering of `X` if
it restricts to zero on each member of some `τ'`-cover of the terminal object of `Over X`. -/
abbrev becomesTrivialOnTauPrimeCovering
    (τPrime : GrothendieckTopology C) (X : C)
    [HasSheafify (τ.over X) AddCommGrpCat]
    [HasExt (Sheaf (τ.over X) AddCommGrpCat)]
    (ℱ : Sheaf (τ.over X) AddCommGrpCat) (n : ℕ)
    (ξ : terminalOverCohomology ℱ (n + 1)) : Prop :=
  ∃ T : (τPrime.over X).Cover (terminalOver X), ∀ I : T.Arrow,
    (((ℱ.cohomologyPresheaf (n + 1)).map I.f.op) ξ = 0)

/-- The predicate cutting out the degree-`n + 1` classes on `(C_τ/X)` that are locally trivial on
some `τ'`-covering of `X`. -/
abbrev locallyTrivialOnTauPrimeCovering
    (τPrime : GrothendieckTopology C) (X : C)
    [HasSheafify (τ.over X) AddCommGrpCat]
    [HasExt (Sheaf (τ.over X) AddCommGrpCat)]
    (ℱ : Sheaf (τ.over X) AddCommGrpCat) (n : ℕ) :
    terminalOverCohomology ℱ (n + 1) → Prop :=
  fun ξ ↦ becomesTrivialOnTauPrimeCovering τPrime X ℱ n ξ

-- Proof sketch: apply the Leray spectral sequence for the localized topology-comparison morphism
-- `ε_X`. The hypothesis `(V_n)` kills the terms `E₂^{p,q}` with `p > 0` and `1 ≤ q ≤ n`, so the
-- edge morphism in total degree `n + 1` is injective. The following map to
-- `H^0_{τ'}(X, R^{n + 1} ε_{X,*} \mathcal F)` detects precisely the classes whose restrictions
-- vanish on a `τ'`-covering of `X`.
/-- Lemma 21.30.5: assume `τ' ≤ τ` and the vanishing condition `(V_n)` for a sheaf
`\mathcal F` on `(C_\tau / X)`. Then there exists a degree-`n + 1` comparison morphism from the
`τ'`-cohomology of `ε_{X,*}\mathcal F` to the `τ`-cohomology of `\mathcal F`, written here in the
terminal-over-site formulation, whose underlying function is injective and whose image consists
exactly of the classes that become zero on some `τ'`-covering of `X`. -/
theorem exists_objectwiseLocalizedComparison_injective_with_locallyTrivial_image_of_VCondition
    (hle : τ' ≤ τ) (X : C)
    [HasSheafify (τ.over X) AddCommGrpCat]
    [HasExt (Sheaf (τ.over X) AddCommGrpCat)]
    [HasSheafify (τ'.over X) AddCommGrpCat]
    [HasExt (Sheaf (τ'.over X) AddCommGrpCat)]
    [HasInjectiveResolutions (Sheaf (τ.over X) AddCommGrpCat)]
    (ℱ : Sheaf (τ.over X) AddCommGrpCat)
    (n : ℕ) (hVn : localizedComparisonVCondition hle X ℱ n) :
    ∃ comparison :
      terminalOverCohomology ((localizedTopologyComparisonPushforwardAb' hle X).obj ℱ) (n + 1) ⟶
        terminalOverCohomology ℱ (n + 1),
      Function.Injective comparison ∧
        ∀ ξ : terminalOverCohomology ℱ (n + 1),
          (∃ η :
            terminalOverCohomology
              ((localizedTopologyComparisonPushforwardAb' hle X).obj ℱ) (n + 1),
              comparison η = ξ) ↔
            locallyTrivialOnTauPrimeCovering τ' X ℱ n ξ := sorry

end CategoryTheory.GrothendieckTopology

/-! ### Lemma_21_30_6 (from Chap21) -/
open CategoryTheory CategoryTheory.Limits

universe u v w

noncomputable section

/-- A source-facing abstraction of the setup used to compare `τ`- and `τ'`-cohomology. -/
structure ComparingCohomologySituation (C : Type u) [Category.{v} C] [HasPullbacks C] where
  tau : GrothendieckTopology C
  tauPrime : GrothendieckTopology C
  P : MorphismProperty C
  coeff : C → Type w
  cohomology : ∀ {Y : C}, ℕ → coeff Y → Over Y → Type w
  cohomologyGroup : ∀ {Y : C} (n : ℕ) (F : coeff Y) (U : Over Y),
    AddCommGroup (cohomology n F U)
  map : ∀ {Y : C} (n : ℕ) (F : coeff Y) {U V : Over Y}, (U ⟶ V) →
    cohomology n F V → cohomology n F U

attribute [instance] ComparingCohomologySituation.cohomologyGroup

/-- The object of `Over Y` corresponding to the base change `X ×_Y Z → Y`. -/
abbrev baseChangeOver {C : Type u} [Category.{v} C] [HasPullbacks C] {X Y Z : C}
    (f : X ⟶ Y) (g : Z ⟶ Y) : Over Y :=
  Over.mk (pullback.fst f g ≫ f)

/-- The structure map of `baseChangeOver f g` is the first pullback projection followed by `f`. -/
-- Proof sketch: unfold `baseChangeOver` and `Over.mk`.
theorem baseChangeOver_hom {C : Type u} [Category.{v} C] [HasPullbacks C] {X Y Z : C}
    (f : X ⟶ Y) (g : Z ⟶ Y) :
    (baseChangeOver f g).hom = pullback.fst f g ≫ f := sorry

/-- In the self-pullback of `f`, the second projection composed with `f` equals the first. -/
-- Proof sketch: this is the pullback commutativity relation for the square defined by `f`.
theorem self_pullback_snd_comp_eq {C : Type u} [Category.{v} C] [HasPullbacks C] {X Y : C}
    (f : X ⟶ Y) :
    pullback.snd f f ≫ f = pullback.fst f f ≫ f := sorry

/-- Lemma 21.30.6: if a class in `H^(n + 1)(X, F')` has equal pullbacks to `X ×_Y X`, then after
some `τ'`-covering of `Y` its pullback to each `Yᵢ ×_Y X` vanishes. -/
-- Proof sketch: reinterpret `θ` as a section of the higher direct image on `Y`, use the equality
-- on `X ×_Y X` to show its pullback to `X` is zero, and then apply the `τ`-sheaf property together
-- with trivial base change to obtain a `τ'`-covering on which the class vanishes.
theorem equalizer_class_vanishes_after_tauPrime_cover
    {C : Type u} [Category.{v} C] [HasPullbacks C]
    (S : ComparingCohomologySituation C) {X Y : C} (f : X ⟶ Y)
    (hfP : S.P f)
    (hfcover : Sieve.generateFamily (fun _ : PUnit ↦ X) (fun _ ↦ f) ∈ S.tau Y)
    (F : S.coeff Y) (n : ℕ)
    (θ : S.cohomology (n + 1) F (Over.mk f))
    (hθ :
      S.map (n + 1) F
          (((Over.homMk (pullback.fst f f)) : baseChangeOver f f ⟶ Over.mk f)) θ =
        S.map (n + 1) F
          (((Over.homMk (pullback.snd f f) (self_pullback_snd_comp_eq f)) :
              baseChangeOver f f ⟶ Over.mk f)) θ) :
    ∃ (ι : Type (max u v w)) (Yᵢ : ι → C) (π : ∀ i, Yᵢ i ⟶ Y),
      Sieve.generateFamily Yᵢ π ∈ S.tauPrime Y ∧
      ∀ i,
        S.map (n + 1) F
            (((Over.homMk (pullback.fst f (π i))) : baseChangeOver f (π i) ⟶ Over.mk f)) θ = 0 :=
  sorry

/-! ### Lemma_21_30_7 (from Chap21) -/
open CategoryTheory Opposite

noncomputable section

universe u

namespace CategoryTheory.GrothendieckTopology

variable {C : Type u} [Category.{u} C]
variable {τ τ' : GrothendieckTopology C}
variable (P : MorphismProperty C)
variable (A' : ∀ X : C, ObjectProperty (Sheaf (τ'.over X) AddCommGrpCat.{u}))

variable [∀ X : C, HasInjectiveResolutions (Sheaf (τ'.over X) AddCommGrpCat.{u})]
variable [∀ {X Y : C} (f : X ⟶ Y),
  Functor.Additive
    ((Over.map f).sheafPushforwardCocontinuous AddCommGrpCat.{u}
      (τ'.over X) (τ'.over Y))]

-- Proof sketch: this is exactly the coarser-topology sheaf condition supplied by
-- `Situation 21.30.1` for every object of `A'_X`.
/-- In Situation `21.30.1`, each object of `A'_X` may be regarded as a sheaf for the coarser
topology `τ.over X`. -/
theorem comparisonObject_isSheafForCoarser
    (h : cohomology_comparison_situation τ τ' P A')
    {X : C} {ℱ : Sheaf (τ'.over X) AddCommGrpCat.{u}}
    (hℱ : A' X ℱ) :
    CategoryTheory.Presheaf.IsSheaf (τ.over X) ℱ.1 :=
  h.isSheaf_for_coarser_topology hℱ

/-- An object of `A'_X` viewed as a sheaf for the coarser topology `τ.over X`. -/
abbrev comparisonObjectAsCoarserSheaf
    (h : cohomology_comparison_situation τ τ' P A')
    {X : C} (ℱ : Sheaf (τ'.over X) AddCommGrpCat.{u}) (hℱ : A' X ℱ) :
    Sheaf (τ.over X) AddCommGrpCat.{u} :=
  ⟨ℱ.1, comparisonObject_isSheafForCoarser P A' h hℱ⟩

variable [∀ X : C, HasSheafify (τ.over X) AddCommGrpCat.{u}]
variable [∀ X : C, HasExt (Sheaf (τ.over X) AddCommGrpCat.{u})]

/-- A degree-`n + 1` cohomology class on an object `U/X` of the localized `τ`-site is locally
zero for `τ'` if it restricts to zero on each member of some `τ'`-covering of `U` over `X`. -/
abbrev localizedComparisonObjectwiseCohomology
    {X : C}
    (ℱ : Sheaf (τ.over X) AddCommGrpCat.{u})
    (U : Over X) (n : ℕ) : AddCommGrpCat.{u} :=
  (ℱ.cohomologyPresheaf (n + 1)).obj (op U)

/-- A degree-`n + 1` cohomology class on an object `U/X` of the localized `τ`-site is locally
zero for `τ'` if it restricts to zero on each member of some `τ'`-covering of `U` over `X`. -/
abbrev localizedComparisonClassLocallyZero
    {X : C}
    (ℱ : Sheaf (τ.over X) AddCommGrpCat.{u})
    (U : Over X) (n : ℕ)
    (ξ : localizedComparisonObjectwiseCohomology ℱ U n) : Prop :=
  ∃ T : (τ'.over X).Cover U, ∀ I : T.Arrow,
    (((ℱ.cohomologyPresheaf (n + 1)).map I.f.op) ξ = 0)

/-- The source-facing comparison condition `(V_n)` says that for every `X`, every sheaf
`\mathcal F ∈ A_X`, every object `U/X`, and every class in `H^{n + 1}_τ(U, \mathcal F)`, the
class becomes zero after passing to a `τ'`-covering of `U`. -/
def localizedComparisonLocalVanishingCondition
    (h : cohomology_comparison_situation τ τ' P A')
    (n : ℕ) : Prop :=
  ∀ (X : C) (ℱ : Sheaf (τ'.over X) AddCommGrpCat.{u}),
    (hℱ : A' X ℱ) →
      ∀ (U : Over X)
        (ξ :
          localizedComparisonObjectwiseCohomology
            (comparisonObjectAsCoarserSheaf P A' h ℱ hℱ) U n),
        @localizedComparisonClassLocallyZero C _ τ τ' _ _ X
          (comparisonObjectAsCoarserSheaf P A' h ℱ hℱ) U n ξ

-- Proof sketch: start with a class `ξ ∈ H^{n + 2}_τ(U, \mathcal F)` for `\mathcal F ∈ A_X` and
-- use locality to reduce to the case of a singleton `τ`-cover in the morphism property `P`.
-- Lemma `21.30.5` identifies the pullback of `ξ` with a unique `τ'`-class, Lemma `21.30.6`
-- kills that class after a `τ'`-covering, and Lemma `21.30.4` plus the truncation triangle and
-- Lemma `21.20.5` show that `ξ` comes from `τ'`-cohomology. Locality of `τ'`-cohomology then
-- yields the desired `τ'`-local vanishing of `ξ`.
/-- Lemma 21.30.7: in Situation 21.30.1, the local comparison vanishing condition `(V_n)`
implies the next-step condition `(V_{n + 1})`. -/
theorem localizedComparisonLocalVanishingCondition_succ
    (h : cohomology_comparison_situation τ τ' P A')
    (n : ℕ)
    (hVn : localizedComparisonLocalVanishingCondition P A' h n) :
    localizedComparisonLocalVanishingCondition P A' h (n + 1) := sorry

end CategoryTheory.GrothendieckTopology

/-! ### Lemma_21_30_8 (from Chap21) -/
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

/-! ### Lemma_21_30_9 (from Chap21) -/
open CategoryTheory
open CategoryTheory.GrothendieckTopology
open CategoryTheory.ObjectProperty

noncomputable section

attribute [local instance] HasDerivedCategory.standard

universe u v

namespace CategoryTheory.GrothendieckTopology

section

variable {C : Type u} [Category.{v} C]
variable {τ τ' : GrothendieckTopology C}

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

/-- The source-side comparison subcategory `A_X ⊂ \operatorname{Ab}(\mathcal C_\tau/X)` obtained
by pulling back `A'_X` along the localized comparison direct image `\epsilon_{X,*}`. -/
abbrev comparisonSourceObjectProperty
    (hle : τ' ≤ τ)
    (A' : ∀ X : C, ObjectProperty (Sheaf (τ'.over X) AddCommGrpCat.{max u v}))
    (X : C) :
    ObjectProperty (Sheaf (τ.over X) AddCommGrpCat.{max u v}) :=
  (A' X).inverseImage (comparisonTopologyPushforwardAb hle X)

/-- The bounded-below derived full subcategory on `(C_τ/X)` cut out by the pulled-back
comparison subcategory `A_X`. -/
abbrev comparisonSourceDerivedPlus
    (hle : τ' ≤ τ)
    (A' : ∀ X : C, ObjectProperty (Sheaf (τ'.over X) AddCommGrpCat.{max u v}))
    (X : C) :=
  (localizedDerivedPlusCohomologyInProperty (τ.over X)
    (comparisonSourceObjectProperty hle A' X)).FullSubcategory

/-- The bounded-below derived full subcategory on `(C_{τ'}/X)` cut out by `A'_X`. -/
abbrev comparisonTargetDerivedPlus
    (A' : ∀ X : C, ObjectProperty (Sheaf (τ'.over X) AddCommGrpCat.{max u v}))
    (X : C) :=
  (localizedDerivedPlusCohomologyInProperty (τ'.over X) (A' X)).FullSubcategory

-- Proof sketch: transport kernels and cokernels in `A_X` by applying `ε_{X,*}` and use that
-- `A'_X` is weak LinearRepresentations_Serre_1977 by the comparison situation. For extensions, apply `ε_{X,*}` to a short
-- exact sequence in `Ab(C_τ/X)`, use Lemma `21.30.8` to kill `R¹ ε_{X,*}` on the left term, and
-- then pull the middle term back along `ε_X^{-1}`.
/-- Lemma 21.30.9 (1): in Situation `21.30.1`, for every `X ∈ \mathcal C` the pulled-back
comparison subcategory `\mathcal A_X ⊂ \operatorname{Ab}(\mathcal C_\tau / X)` is a weak LinearRepresentations_Serre_1977
subcategory. -/
theorem comparisonObjectProperty_isWeakSerreSubcategory
    (h : @cohomology_comparison_situation _ _ τ τ' _ _ _ P A')
    (X : C) :
    IsWeakSerreClass (comparisonSourceObjectProperty hle A' X) := sorry

/-- The pulled-back comparison subcategory `A_X` inherits a weak LinearRepresentations_Serre_1977 structure from
Lemma `21.30.9 (1)`. -/
instance instComparisonObjectPropertyIsWeakSerreClass
    (h : @cohomology_comparison_situation _ _ τ τ' _ _ _ P A')
    (X : C) :
    IsWeakSerreClass (comparisonSourceObjectProperty hle A' X) :=
  comparisonObjectProperty_isWeakSerreSubcategory hle P A' h X

-- Proof sketch: exact inverse image preserves bounded-belowness and commutes with cohomology.
-- For each cohomology sheaf in `A'_X`, the degree-zero case of Lemma `21.30.8 (2)` identifies
-- `ε_{X,*}(ε_X^{-1} \mathcal F')` with an object of `A'_X`, which is exactly the defining
-- condition for membership in `A_X`.
/-- The restricted inverse-image functor `\epsilon_X^{-1}` sends
`D^+_{\mathcal A'_X}(\mathcal C_{\tau'}/X)` into `D^+_{\mathcal A_X}(\mathcal C_\tau/X)`. -/
theorem comparisonPullbackDerived_obj_mem_plusCohomologyIn
    (h : @cohomology_comparison_situation _ _ τ τ' _ _ _ P A')
    (X : C)
    (K : comparisonTargetDerivedPlus A' X) :
    localizedDerivedPlusCohomologyInProperty (τ.over X)
      (comparisonSourceObjectProperty hle A' X)
      ((ObjectProperty.ι
        (localizedDerivedPlusCohomologyInProperty (τ'.over X) (A' X)) ⋙
          epsilonInvDerived hle X).obj K) := sorry

/-- The restriction of `\epsilon_X^{-1}` to the bounded-below derived subcategory with cohomology
in `A'_X`. -/
abbrev comparisonPullbackDerivedPlusWithCohomologyIn
    (h : @cohomology_comparison_situation _ _ τ τ' _ _ _ P A')
    (X : C) :
    comparisonTargetDerivedPlus A' X ⥤ comparisonSourceDerivedPlus hle A' X :=
  ObjectProperty.lift
    (localizedDerivedPlusCohomologyInProperty (τ.over X)
      (comparisonSourceObjectProperty hle A' X))
    (ObjectProperty.ι (localizedDerivedPlusCohomologyInProperty (τ'.over X) (A' X)) ⋙
      epsilonInvDerived hle X)
    (comparisonPullbackDerived_obj_mem_plusCohomologyIn hle P A' h X)

-- Proof sketch: apply the bounded-below comparison theorem from Lemma `21.28.5` in the localized
-- setting, with source weak LinearRepresentations_Serre_1977 subcategory `A_X`, target weak LinearRepresentations_Serre_1977 subcategory `A'_X`, exact
-- inverse image `ε_X^{-1}`, and unit isomorphisms supplied by Lemma `21.30.8 (2)`.
/-- The restricted right-derived direct image `R\epsilon_{X,*}` on the bounded-below derived
subcategory with cohomology in `A_X`. It is the quasi-inverse promised by Lemma `21.30.9 (2)`. -/
theorem comparisonPushforwardDerived_obj_mem_plusCohomologyIn
    (h : @cohomology_comparison_situation _ _ τ τ' _ _ _ P A')
    (X : C)
    (K : comparisonSourceDerivedPlus hle A' X) :
    localizedDerivedPlusCohomologyInProperty (τ'.over X) (A' X)
      ((ObjectProperty.ι
        (localizedDerivedPlusCohomologyInProperty (τ.over X)
          (comparisonSourceObjectProperty hle A' X)) ⋙
          rEpsilonDerived hle X).obj K) := sorry

/-- The restriction of `R\epsilon_{X,*}` to the bounded-below derived subcategory with cohomology
in `A_X`. -/
abbrev comparisonPushforwardDerivedPlusWithCohomologyIn
    (h : @cohomology_comparison_situation _ _ τ τ' _ _ _ P A')
    (X : C) :
    comparisonSourceDerivedPlus hle A' X ⥤ comparisonTargetDerivedPlus A' X :=
  ObjectProperty.lift
    (localizedDerivedPlusCohomologyInProperty (τ'.over X) (A' X))
    (ObjectProperty.ι
      (localizedDerivedPlusCohomologyInProperty (τ.over X)
        (comparisonSourceObjectProperty hle A' X)) ⋙
        rEpsilonDerived hle X)
    (comparisonPushforwardDerived_obj_mem_plusCohomologyIn hle P A' h X)

-- Proof sketch: after clause `(1)`, the source subcategory `A_X` is weak LinearRepresentations_Serre_1977. Lemma
-- `21.30.8 (2)` identifies the unit `K' ⟶ R ε_{X,*}(ε_X^{-1} K')` on every object of
-- `D^+_{A'_X}`, and Lemma `21.28.5` then upgrades these unit isomorphisms to an equivalence of
-- bounded-below derived subcategories, with quasi-inverse the restricted `ε_X^{-1}`.
/-- Lemma 21.30.9 (2): in Situation `21.30.1`, for every `X ∈ \mathcal C` the functor
`R\epsilon_{X,*} : D^+_{\mathcal A_X}(\mathcal C_\tau / X) \to
D^+_{\mathcal A'_X}(\mathcal C_{\tau'}/X)` is an equivalence of categories, with quasi-inverse
given by the restricted inverse-image functor `\epsilon_X^{-1}`. -/
theorem comparisonPushforwardDerivedPlusWithCohomologyIn_isEquivalence
    (h : @cohomology_comparison_situation _ _ τ τ' _ _ _ P A')
    (X : C) :
    Functor.IsEquivalence
      (comparisonPushforwardDerivedPlusWithCohomologyIn hle P A' h X) := sorry

end

end CategoryTheory.GrothendieckTopology

/-! ### Lemma_21_30_10 (from Chap21) -/
open CategoryTheory
open ComplexShape

noncomputable section

attribute [local instance] HasDerivedCategory.standard

universe u v

namespace CategoryTheory.GrothendieckTopology

variable {C : Type u} [Category.{v} C]
variable {τ τ' : GrothendieckTopology C}

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

/-- The inverse-image functor `\epsilon_X^{-1}` on abelian sheaves for the localized comparison
of the topologies `τ` and `τ'`. -/
noncomputable abbrev comparisonTopologyPullbackAb
    (hle : τ' ≤ τ) (X : C) :
    Sheaf (τ'.over X) AddCommGrpCat.{max u v} ⥤
      Sheaf (τ.over X) AddCommGrpCat.{max u v} :=
  let _ : Functor.IsContinuous (𝟭 (Over X)) (τ'.over X) (τ.over X) :=
    CategoryTheory.id_isContinuous_of_le
      (comparisonOver_le hle X)
  (𝟭 (Over X)).sheafPullback AddCommGrpCat.{max u v} (τ'.over X) (τ.over X)

/-- The bounded-below derived objects on `(C_J/X)` whose cohomology sheaves all lie in the
chosen object property `A`. -/
abbrev localizedDerivedPlusCohomologyInProperty
    {X : C}
    (J : GrothendieckTopology (Over X))
    (A : ObjectProperty (Sheaf J AddCommGrpCat.{max u v})) :
    ObjectProperty (DerivedCategory (Sheaf J AddCommGrpCat.{max u v})) :=
  fun K ↦
    (∀ i : ℤ,
      A ((DerivedCategory.homologyFunctor (Sheaf J AddCommGrpCat.{max u v}) i).obj K)) ∧
      ∃ n : ℤ, ∀ i : ℤ, i < n →
        Limits.IsZero
          ((DerivedCategory.homologyFunctor (Sheaf J AddCommGrpCat.{max u v}) i).obj K)

/-- The degree-`n` hypercohomology object of a derived abelian sheaf on a localized site,
computed by a chosen derived global-sections functor. -/
abbrev localizedSiteHypercohomology
    {X : C} {J : GrothendieckTopology (Over X)}
    (RGamma : DerivedCategory (Sheaf J AddCommGrpCat.{max u v}) ⥤
      DerivedCategory AddCommGrpCat.{max u v})
    (L : DerivedCategory (Sheaf J AddCommGrpCat.{max u v})) (n : ℕ) :
    AddCommGrpCat.{max u v} :=
  (DerivedCategory.homologyFunctor AddCommGrpCat.{max u v} (n : ℤ)).obj (RGamma.obj L)

-- Proof sketch: regard `F'` as a derived object concentrated in degree `0`, apply the derived
-- comparison from Lemma `21.30.8 (2)`, and then evaluate global sections. Remark `21.14.4`
-- identifies the derived global sections of `R ε_{X,*}(ε_X^{-1} F')` with those of
-- `ε_X^{-1} F'`, yielding the comparison on degree-`n` cohomology groups.
/-- Lemma 21.30.10 (1): in Situation `21.30.1`, for `F' ∈ \mathcal A'_X` the degree-`n`
cohomology of `F'` on `(C_{\tau'}/X)` is canonically isomorphic to the degree-`n` cohomology of
`\epsilon_X^{-1}F'` on `(C_\tau/X)`. -/
theorem comparisonTopologyPullback_cohomology_isomorphic_of_mem
    (h : ComparisonSituation P A')
    (X : C)
    (F' : Sheaf (τ'.over X) AddCommGrpCat.{max u v})
    (hF' : A' X F')
    (n : ℕ) :
    IsIsomorphic
      ((Sheaf.cohomologyFunctor (τ'.over X) n).obj F')
      ((Sheaf.cohomologyFunctor (τ.over X) n).obj
        ((comparisonTopologyPullbackAb hle X).obj F')) := sorry

-- Proof sketch: Lemma `21.30.8 (2)` identifies `K'` with
-- `R ε_{X,*}(ε_X^{-1} K')` for every `K' ∈ D^+_{\mathcal A'_X}(C_{τ'}/X)`. Applying the
-- comparison of derived global sections from Remark `21.14.4` to `ε_X^{-1} K'` and then taking
-- degree-`n` homology gives the stated hypercohomology comparison.
/-- Lemma 21.30.10 (2): in Situation `21.30.1`, if
`K' ∈ D^+_{\mathcal A'_X}(\mathcal C_{\tau'}/X)`, then the degree-`n` hypercohomology of `K'` on
`(C_{\tau'}/X)` is canonically isomorphic to the degree-`n` hypercohomology of
`\epsilon_X^{-1}K'` on `(C_\tau/X)`. -/
theorem comparisonTopologyPullback_hypercohomology_isomorphic_of_plusCohomologyIn
    (h : ComparisonSituation P A')
    (X : C)
    (epsilonInverseImageDerived : ∀ X : C,
      DerivedCategory (Sheaf (τ'.over X) AddCommGrpCat.{max u v}) ⥤
        DerivedCategory (Sheaf (τ.over X) AddCommGrpCat.{max u v}))
    (epsilonPushforwardDerived : ∀ X : C,
      DerivedCategory (Sheaf (τ.over X) AddCommGrpCat.{max u v}) ⥤
        DerivedCategory (Sheaf (τ'.over X) AddCommGrpCat.{max u v}))
    (RGammaTau : ∀ X : C,
      DerivedCategory (Sheaf (τ.over X) AddCommGrpCat.{max u v}) ⥤
        DerivedCategory AddCommGrpCat.{max u v})
    (RGammaTau' : ∀ X : C,
      DerivedCategory (Sheaf (τ'.over X) AddCommGrpCat.{max u v}) ⥤
        DerivedCategory AddCommGrpCat.{max u v})
    (hDerivedComparison :
      ∀ (X : C) (K' : DerivedCategory (Sheaf (τ'.over X) AddCommGrpCat.{max u v})),
        localizedDerivedPlusCohomologyInProperty (τ'.over X) (A' X) K' →
          IsIsomorphic
            K'
            ((epsilonPushforwardDerived X).obj ((epsilonInverseImageDerived X).obj K')))
    (hGlobalSectionsComparison :
      ∀ (X : C) (L : DerivedCategory (Sheaf (τ.over X) AddCommGrpCat.{max u v})),
        IsIsomorphic
          ((RGammaTau' X).obj ((epsilonPushforwardDerived X).obj L))
          ((RGammaTau X).obj L))
    (K' : DerivedCategory (Sheaf (τ'.over X) AddCommGrpCat.{max u v}))
    (hK' :
      localizedDerivedPlusCohomologyInProperty (τ'.over X) (A' X) K')
    (n : ℕ) :
    IsIsomorphic
      (localizedSiteHypercohomology (RGammaTau' X) K' n)
      (localizedSiteHypercohomology (RGammaTau X)
        ((epsilonInverseImageDerived X).obj K') n) := sorry

end CategoryTheory.GrothendieckTopology
