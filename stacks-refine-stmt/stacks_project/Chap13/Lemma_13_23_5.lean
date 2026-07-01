import Mathlib
import Mathlib.Algebra.Homology.CochainComplexPlus
import Mathlib.Algebra.Homology.HomotopyCategory.Triangulated
import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory
import Mathlib.CategoryTheory.Triangulated.Subcategory
import stacks_project.Chap13.Definition_13_18_1
import stacks_project.Chap13.Lemma_13_11_6

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open CategoryTheory
open CategoryTheory.ObjectProperty
open ComplexShape
open scoped CategoryTheory

universe v u

namespace CategoryTheory

variable {𝒜 : Type u} [Category.{v} 𝒜] [Abelian 𝒜]

/- Domain-style sampling for Lemma 13.23.5:
- primary domain: bounded-below injective complexes in the homotopy category and exact functors
  between triangulated categories;
- sampled owner declarations:
  `CochainComplex.InjectivePlus`,
  `CochainComplex.InjectivePlus.toHomotopy`,
  `Functor.CommShift`,
  `Functor.IsTriangulated`;
- best owner abstraction: the source-facing owners in this file are the full subcategory
  `K^+(\mathcal I) ⊆ K^+(\mathcal A)` and the corresponding homotopy resolution functor, while
  exactness itself is owned canonically upstream by `Functor.CommShift` together with
  `Functor.IsTriangulated`;
- primitive-vs-derived split:
  primitive data: the chapter owner `CochainComplex.InjectivePlus 𝒜`, its homotopy-category image,
    a functor into that full subcategory, and the comparison natural transformation from the
    identity;
  derived API: the triangulated instance on the injective subcategory and the exactness statement
    for the chosen resolution functor.

Source/core/bridge triage:
- `source-facing`: `HomotopyResolutionFunctor`;
- `core/canonical`: `CochainComplex.InjectivePlus` for the complex-level injective owner and the
  exact-functor owners `Functor.CommShift` and `Functor.IsTriangulated`;
- `bridge/view`: `boundedBelowInjectiveHomotopyProperty`, `boundedBelowInjectiveHomotopyCat`, and
  `CochainComplex.InjectivePlus.toHomotopy`, which pass from bounded-below injective complexes to
  their homotopy-category image before expressing exactness in the canonical triangulated API.
-/

/-- The object property on `K^+(\mathcal A)` cutting out the bounded-below complexes whose terms
are injective objects of `𝒜`, read via the chapter owner `CochainComplex.InjectivePlus 𝒜`. -/
abbrev boundedBelowInjectiveHomotopyProperty (𝒜 : Type u)
    [Category.{v} 𝒜] [Abelian 𝒜] :
    ObjectProperty (K⁺(𝒜)) :=
  fun K ↦
    let C : CochainComplex 𝒜 ℤ := K.obj.as
    ∀ n : ℤ, Injective (C.X n)

/-- The bounded-below homotopy category `K^+(\mathcal I)` of complexes of injective objects in
`𝒜`. -/
abbrev boundedBelowInjectiveHomotopyCat (𝒜 : Type u)
    [Category.{v} 𝒜] [Abelian 𝒜] :=
  (boundedBelowInjectiveHomotopyProperty 𝒜).FullSubcategory

/- The textbook category `K^+(\mathcal I)` depends on the ambient abelian category `𝒜` through
its injective objects. The scoped notation `K⁺ᵢ(𝒜)` keeps that ambient parameter explicit on the
Lean theorem surface while replacing the raw owner name. -/
scoped[CategoryTheory] notation:max "K⁺" "ᵢ(" A:arg ")" => boundedBelowInjectiveHomotopyCat A

namespace CochainComplex.InjectivePlus

/-- The quotient bridge from bounded-below complexes of injectives to their image
`K^+(\mathcal I) ⊆ K^+(\mathcal A)`. -/
abbrev toHomotopy (𝒜 : Type u) [Category.{v} 𝒜] [Abelian 𝒜] :
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

-- Proof sketch: the shift of a bounded-below complex of injectives is again termwise injective,
-- and the cone of a morphism between such complexes has terms built from finite biproducts of
-- injectives, so it stays inside the same triangulated object property.
/-- The bounded-below injective object property on `K^+(\mathcal A)` is triangulated. -/
instance boundedBelowInjectiveHomotopyProperty_isTriangulated :
    ObjectProperty.IsTriangulated (boundedBelowInjectiveHomotopyProperty 𝒜) := sorry

/-- A resolution functor on `K^+(\mathcal A)` is a functor from the bounded-below homotopy
category to the full triangulated subcategory of bounded-below complexes of injectives, together
with a natural quasi-isomorphism from the identity functor after forgetting injectivity. -/
structure HomotopyResolutionFunctor (𝒜 : Type u) [Category.{v} 𝒜] [Abelian 𝒜] where
  /-- The underlying functor `K^+(\mathcal A) ⥤ K^+(\mathcal I)`. -/
  toFunctor : K⁺(𝒜) ⥤ K⁺ᵢ(𝒜)
  /-- The comparison morphism from a bounded-below complex to its chosen injective resolution. -/
  ι : 𝟭 (K⁺(𝒜)) ⟶
    toFunctor ⋙ ObjectProperty.ι (boundedBelowInjectiveHomotopyProperty 𝒜)
  /-- The comparison morphism is a quasi-isomorphism in `K^+(\mathcal A)` on every object. -/
  quasiIso_app (K : K⁺(𝒜)) : Qis⁺(𝒜) (ι.app K)

namespace HomotopyResolutionFunctor

-- Proof sketch: for each `n : ℤ`, compare the two injective resolutions `j(K⟦n⟧)` and
-- `j(K)⟦n⟧` of the shifted object `K⟦n⟧`. Lemmas 13.18.6 and 13.18.7 give a unique comparison
-- isomorphism compatible with the quasi-isomorphisms from `K⟦n⟧`, and these isomorphisms assemble
-- functorially into a `CommShift ℤ` structure. For a distinguished triangle
-- `(K, L, M, f, g, h)`, the comparison quasi-isomorphisms identify the image triangle
-- `(j(K), j(L), j(M), j(f), j(g), ξ_K ≫ j(h))` with a distinguished triangle in `D^+(\mathcal A)`;
-- Proposition 13.23.1 and Lemma 13.4.18 then imply that it is distinguished already in
-- `K^+(\mathcal I)`.
/-- Lemma 13.23.5: any resolution functor
`j : K^+(\mathcal A) ⥤ K^+(\mathcal I)` is exact, i.e. admits a shift-commuting structure for
which it is triangulated. -/
theorem toFunctor_exact (j : HomotopyResolutionFunctor 𝒜) :
    ∃ hcomm : j.toFunctor.CommShift ℤ,
      letI : j.toFunctor.CommShift ℤ := hcomm
      j.toFunctor.IsTriangulated := sorry

end HomotopyResolutionFunctor

end CategoryTheory
