import Mathlib
import StacksProject_2024.Chap13.Definition_13_18_1

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open CategoryTheory.ObjectProperty
open ComplexShape
open scoped CategoryTheory

universe v u

namespace CochainComplex

variable (𝒜 : Type u) [Category.{v} 𝒜] [Abelian 𝒜]

/-
Domain-style sampling:
- primary domain: bounded-below injective resolutions of cochain complexes;
- sampled owner declarations:
  `CochainComplex.InjectiveResolution`,
  `CochainComplex.InjectiveResolution.injective`,
  `CochainComplex.InjectiveResolution.quasiIso`,
  `CategoryTheory.HomotopyResolutionFunctor`;
- best owner abstraction: `CochainComplex.InjectiveResolution` already owns the chosen resolving
  complex, comparison map, bounded-below structure, and termwise-injective/quasi-isomorphism API
  for a single bounded-below complex;
- primitive data here: only the objectwise assignment `K ↦ InjectiveResolution K`;
- derived API here: the chosen complex, the comparison map, and the basic resolution facts, all of
  which should be read directly from the owner `InjectiveResolution` instead of being re-exported
  under parallel local names.

Source/core/bridge triage:
- `source-facing`: `ResolutionFunctorOne` is the Stacks-definition objectwise choice of bounded-
  below injective resolutions;
- `core/canonical`: `CochainComplex.InjectiveResolution` is the project owner for the data of a
  chosen injective resolution of one complex;
- `bridge/view`: later files build the homotopy-category realization from this objectwise choice.
-/
/-- Definition 13.23.2: a resolution functor 1 on an abelian category assigns to each
bounded-below cochain complex `K : Plus 𝒜` a chosen bounded-below injective resolution of
`K`, namely an element of the canonical owner `InjectiveResolution K.obj`. -/
@[stacks 013W]
abbrev ResolutionFunctorOne :=
  (K : Plus 𝒜) → InjectiveResolution K.obj

end CochainComplex

namespace CategoryTheory

variable (𝒜 : Type u) [Category.{v} 𝒜] [Abelian 𝒜]

/-- The object property on `K^+(\mathcal A)` cutting out the bounded-below complexes whose terms
are injective objects of `𝒜`. -/
abbrev boundedBelowInjectiveHomotopyProperty :
    ObjectProperty (K⁺(𝒜)) :=
  fun K ↦
    let C : CochainComplex 𝒜 ℤ := K.obj.as
    ∀ n : ℤ, Injective (C.X n)

/-- The bounded-below homotopy category `K^+(\mathcal I)` of complexes of injective objects in
`𝒜`. -/
abbrev boundedBelowInjectiveHomotopyCat :=
  (boundedBelowInjectiveHomotopyProperty 𝒜).FullSubcategory

/- The textbook category `K^+(\mathcal I)` depends on the ambient abelian category `𝒜` through
its injective objects. The scoped notation `K⁺ᵢ(𝒜)` keeps that ambient parameter explicit on the
Lean theorem surface while replacing the raw owner name. -/
scoped[CategoryTheory] notation:max "K⁺" "ᵢ(" A:arg ")" => boundedBelowInjectiveHomotopyCat A

namespace CochainComplex.InjectivePlus

/-- The quotient bridge from bounded-below complexes of injectives to their image
`K^+(\mathcal I) ⊆ K^+(\mathcal A)`. -/
abbrev toHomotopy :
    CochainComplex.InjectivePlus 𝒜 ⥤ K⁺ᵢ(𝒜) :=
  (boundedBelowInjectiveHomotopyProperty 𝒜).lift
    (ObjectProperty.ι
      (fun K : CochainComplex.Plus 𝒜 ↦ ∀ n : ℤ, Injective (K.obj.X n)) ⋙
        HomotopyCategory.Plus.quotient 𝒜)
    (fun I n ↦ by simpa using I.term_mem n)

end CochainComplex.InjectivePlus

namespace boundedBelowInjectiveHomotopyCat

/-- An object of `K^+(\mathcal I)` determines its underlying bounded-below cochain complex of
injective objects. -/
abbrev toInjectivePlus (I : K⁺ᵢ(𝒜)) : CochainComplex.InjectivePlus 𝒜 :=
  let K : K⁺(𝒜) := I.obj
  ⟨⟨K.obj.as, K.property⟩, fun n ↦ by
    simpa using I.property n⟩

end boundedBelowInjectiveHomotopyCat

/-- A resolution functor on `K^+(\mathcal A)` is a functor from the bounded-below homotopy
category to the full subcategory of bounded-below complexes of injectives, together with a
natural quasi-isomorphism from the identity after forgetting injectivity. -/
structure HomotopyResolutionFunctor where
  /-- The underlying functor `K^+(\mathcal A) ⥤ K^+(\mathcal I)`. -/
  toFunctor : K⁺(𝒜) ⥤ K⁺ᵢ(𝒜)
  /-- The comparison morphism from a bounded-below complex to its chosen injective resolution. -/
  ι : 𝟭 (K⁺(𝒜)) ⟶
    toFunctor ⋙ ObjectProperty.ι (boundedBelowInjectiveHomotopyProperty 𝒜)
  /-- The comparison morphism becomes a quasi-isomorphism after forgetting to
  `K(\mathcal A)`. -/
  quasiIso_app (K : K⁺(𝒜)) :
      (HomotopyCategory.quasiIso 𝒜 (up ℤ)).inverseImage
        (HomotopyCategory.plus 𝒜).ι (ι.app K)

end CategoryTheory
