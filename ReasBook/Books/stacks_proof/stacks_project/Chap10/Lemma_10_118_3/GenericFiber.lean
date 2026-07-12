import StacksProject_2024.Chap10.«10_118_3_1»
import StacksProject_2024.Chap10.Lemma_10_5_3
import StacksProject_2024.Chap10.Lemma_10_24_1
import StacksProject_2024.Chap10.Lemma_10_36_23
import Mathlib.Algebra.Module.FinitePresentation
import Mathlib.Algebra.Module.LocalizedModule.Submodule
import Mathlib.RingTheory.FinitePresentation
import Mathlib.RingTheory.Localization.BaseChange
import Mathlib.RingTheory.Localization.Finiteness
import Mathlib.RingTheory.MvPolynomial.Localization
import Mathlib.RingTheory.TensorProduct.Finite
import Mathlib.LinearAlgebra.Isomorphisms
import Mathlib.Tactic.StacksAttribute

-- Declarations for this item will be appended below by the statement pipeline.

universe u v w

section

variable {R : Type u} [CommRing R] [IsDomain R]
variable {S : Type v} [CommRing S] [Algebra R S] [Algebra.FiniteType R S]
variable {M : Type w} [AddCommGroup M] [Module S M] [Module.Finite S M]

open GenericFlatness

/- Domain-style sampling:
* primary domain: generic freeness / generic flatness for finite type algebras and finite modules
  over a domain;
* sampled owner declarations:
  `GenericFlatness.LocalizationCondition`,
  `GenericFlatness.goodLocus`,
  `Module.FinitePresentation.exists_free_localizedModule_powers`,
  `Module.freeLocus`;
* best owner abstraction in this chapter: `LocalizationCondition R S M f`;
* primitive data: the rings/algebra/module and the localization parameter `f`;
* derived API: finite presentation and freeness of `S_f` and `M_f`;
* layer triage: this file is `source-facing`, asserting existence of a localization satisfying the
  chapter owner condition.
-/
/-- Helper for Lemma 10.118.3: after base change to the fraction field of the domain, the generic
fiber algebra is finitely presented because finite type over a field is finitely presented. -/
lemma fractionRing_localized_algebra_finitePresentation :
    let K := FractionRing R
    let Sₖ := Localization (Algebra.algebraMapSubmonoid S (nonZeroDivisors R))
    letI : Algebra K Sₖ := localizationAlgebra (nonZeroDivisors R) S
    Algebra.FinitePresentation K Sₖ := by
  dsimp
  let T : Type _ := TensorProduct R (FractionRing R) S
  let e : T ≃ₐ[FractionRing R]
      Localization (Algebra.algebraMapSubmonoid S (nonZeroDivisors R)) :=
    Localization.tensorRightAlgEquiv (nonZeroDivisors R) S
  letI : Algebra.FiniteType (FractionRing R) T := inferInstance
  letI : IsNoetherianRing (FractionRing R) := inferInstance
  letI : Algebra.FinitePresentation (FractionRing R) T :=
    (Algebra.FinitePresentation.of_finiteType (R := FractionRing R) (A := T)).mp inferInstance
  -- Over the fraction field, the source theorem reduces finite type to finite presentation.
  exact Algebra.FinitePresentation.equiv (R := FractionRing R) e

/-- Helper for Lemma 10.118.3: after base change to the fraction field, the localized finite module
is finitely presented over the generic fiber algebra because that algebra is Noetherian. -/
lemma fractionRing_localized_module_finitePresentation :
    let K := FractionRing R
    let Sₖ := Localization (Algebra.algebraMapSubmonoid S (nonZeroDivisors R))
    let Mₖ := LocalizedModule (Algebra.algebraMapSubmonoid S (nonZeroDivisors R)) M
    letI : Algebra K Sₖ := localizationAlgebra (nonZeroDivisors R) S
    Module.FinitePresentation Sₖ Mₖ := by
  dsimp
  let T : Type _ := TensorProduct R (FractionRing R) S
  let eA : T ≃ₐ[FractionRing R]
      Localization (Algebra.algebraMapSubmonoid S (nonZeroDivisors R)) :=
    Localization.tensorRightAlgEquiv (nonZeroDivisors R) S
  letI : Algebra.FiniteType (FractionRing R) T := inferInstance
  letI : Algebra.FiniteType (FractionRing R)
      (Localization (Algebra.algebraMapSubmonoid S (nonZeroDivisors R))) :=
    Algebra.FiniteType.equiv inferInstance eA
  letI : IsNoetherianRing (Localization (Algebra.algebraMapSubmonoid S (nonZeroDivisors R))) :=
    Algebra.FiniteType.isNoetherianRing (FractionRing R)
      (Localization (Algebra.algebraMapSubmonoid S (nonZeroDivisors R)))
  let eM : LocalizedModule (Algebra.algebraMapSubmonoid S (nonZeroDivisors R)) M ≃ₗ[
      Localization (Algebra.algebraMapSubmonoid S (nonZeroDivisors R))]
      TensorProduct S (Localization (Algebra.algebraMapSubmonoid S (nonZeroDivisors R))) M :=
    LocalizedModule.equivTensorProduct (Algebra.algebraMapSubmonoid S (nonZeroDivisors R)) M
  letI : Module.Finite
      (Localization (Algebra.algebraMapSubmonoid S (nonZeroDivisors R)))
      (TensorProduct S (Localization (Algebra.algebraMapSubmonoid S (nonZeroDivisors R))) M) :=
    inferInstance
  letI : Module.FinitePresentation
      (Localization (Algebra.algebraMapSubmonoid S (nonZeroDivisors R)))
      (TensorProduct S (Localization (Algebra.algebraMapSubmonoid S (nonZeroDivisors R))) M) :=
    Module.finitePresentation_of_finite
      (Localization (Algebra.algebraMapSubmonoid S (nonZeroDivisors R)))
      (TensorProduct S (Localization (Algebra.algebraMapSubmonoid S (nonZeroDivisors R))) M)
  -- The localized module stays finite after localization, hence it is finitely presented over the
  -- Noetherian generic fiber algebra.
  exact Module.FinitePresentation.of_equiv eM.symm

end
