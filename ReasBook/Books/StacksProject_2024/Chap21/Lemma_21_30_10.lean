import Mathlib
import stacks_project.Chap21.«21_30_0_1»
import stacks_project.Chap07.Example_7_14_3
import stacks_project.Chap21.Situation_21_30_1

-- Declarations for this item will be appended below by the statement pipeline.

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
