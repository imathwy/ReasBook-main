import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

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
