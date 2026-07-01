import Mathlib
import Mathlib.CategoryTheory.Localization.Predicate
import stacks_project.Chap04.Lemma_4_2_18
import stacks_project.Chap13.Lemma_13_18_8
import stacks_project.Chap13.Proposition_13_23_1

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.Localization
open CategoryTheory.ObjectProperty
open CochainComplex
open ComplexShape
open DerivedCategory.TStructure
open scoped CategoryTheory

universe v u

attribute [local instance] HasDerivedCategory.standard

namespace CategoryTheory

section

variable {𝒜 : Type u} [Category.{v} 𝒜] [Abelian 𝒜]

local notation "Q" => (mapBoundedBelowHomotopyToDerivedBelow : K⁺(𝒜) ⥤ D⁺(𝒜))
local notation "KinjIncl" =>
  (ObjectProperty.ι (boundedBelowInjectiveHomotopyProperty 𝒜) : K⁺ᵢ(𝒜) ⥤ K⁺(𝒜))
local notation "IToD" => KinjIncl ⋙ Q

/- Domain-style sampling for Lemma 13.23.6:
- primary domain: localization of the bounded-below homotopy category at quasi-isomorphisms and
  the comparison with bounded-below complexes of injectives;
- sampled owner declarations:
  `Functor.IsLocalization`,
  `Localization.lift`,
  `Localization.fac`,
  `Localization.liftNatIso`,
  `ObjectProperty.ι (boundedBelowInjectiveHomotopyProperty 𝒜) ⋙
  mapBoundedBelowHomotopyToDerivedBelow`;
- best owner abstraction: the core/canonical factorization of a resolution functor through
  `D^+(\mathcal A)` is owned by `Localization.lift` for the localization functor
  `Q : K^+(\mathcal A) ⥤ D^+(\mathcal A)`, while the source-facing uniqueness statement should be
  expressed through the canonical lifting isomorphism API rather than by strict functor equality;
- primitive data: the functor `j.toFunctor : K^+(\mathcal A) ⥤ K^+(\mathcal I)` and the fact
  that it inverts bounded-below quasi-isomorphisms;
- derived API: the factorization through `D^+(\mathcal A)` and the resulting quasi-inverse
  equivalence statement for that factorization.

Source/core/bridge triage:
- `source-facing`: the canonical factorization of a homotopy resolution functor through
  `D^+(\mathcal A)` and its uniqueness up to unique isomorphism;
- `core/canonical`: `Localization.lift`, `Localization.fac`, `Localization.liftNatIso`, and
  `Functor.IsLocalization Q (Qis⁺(𝒜))`;
- `bridge/view`: the quasi-inverse natural isomorphisms obtained by combining the canonical lift
  with the bounded-below injective Hom-to-derived bijection.
-/
attribute [local instance] mapBoundedBelowHomotopyToDerivedBelow_isLocalization

namespace HomotopyResolutionFunctor

-- Proof sketch: if `j' : D^+(\mathcal A) ⥤ K^+(\mathcal I)` is any other factorization equipped
-- with an isomorphism `Q ⋙ j' ≅ j.toFunctor`, then both `j'` and `Localization.lift ...` are
-- liftings of the same functor out of `K^+(\mathcal A)`. The existence part is owned canonically
-- by `Localization.fac`, and uniqueness is obtained by applying `Localization.liftNatIso` to the
-- identity isomorphism of `j.toFunctor`.
/-- Lemma 13.23.6, uniqueness companion: any two factorizations of `j.toFunctor` through
`D^+(\mathcal A)` are canonically isomorphic once their comparison with `Q` is specified. -/
noncomputable def lift_unique (j : HomotopyResolutionFunctor 𝒜)
    (j' : D⁺(𝒜) ⥤ K⁺ᵢ(𝒜)) (e : Q ⋙ j' ≅ j.toFunctor) :
    j' ≅ j.lift := by
  letI : Localization.Lifting Q (Qis⁺(𝒜)) j.toFunctor j' := ⟨e⟩
  exact
    Localization.liftNatIso Q (Qis⁺(𝒜)) j.toFunctor j.toFunctor j'
      j.lift (Iso.refl _)

/-- Lemma 13.23.6: the canonical localization lift of a homotopy resolution functor is an
equivalence of categories, with quasi-inverse the canonical functor
`K^+(\mathcal I) ⥤ D^+(\mathcal A)`. -/
theorem lift_isEquivalence (j : HomotopyResolutionFunctor 𝒜) :
    Functor.IsEquivalence j.lift := by
  let _ : Functor.IsEquivalence IToD := by
    simpa using j.toDerived_isEquivalence
  let _ : Functor.IsEquivalence (j.lift ⋙ IToD) :=
    Functor.isEquivalence_of_iso j.lift_unitIso
  exact Functor.isEquivalence_of_comp_right j.lift IToD

end HomotopyResolutionFunctor

end

end CategoryTheory
