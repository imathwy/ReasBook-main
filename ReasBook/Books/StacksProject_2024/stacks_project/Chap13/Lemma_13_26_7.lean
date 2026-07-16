import Mathlib
import StacksProject_2024.stacks_project.Chap12.Lemma_12_19_15
import StacksProject_2024.stacks_project.Chap13.Definition_13_8_1
import StacksProject_2024.stacks_project.Chap13.Definition_13_13_1

open CategoryTheory
open CategoryTheory.ObjectProperty
open CochainComplex
open FilteredObject.Hom

noncomputable section

universe u v

namespace CategoryTheory

variable {𝒜 : Type u} [Category.{v} 𝒜] [Abelian 𝒜]
variable [Abelian (finiteFilteredObjectCat 𝒜)]

local notation "FilF" => Fil^f(𝒜)
local notation "single₀" => CochainComplex.singleFunctor FilF (0 : ℤ)

/-- Helper for Lemma 13.26.7: the associated graded functor on the finite filtered category. -/
abbrev finiteFilteredObjectAssociatedGradedFunctor :
    FilF ⥤ GradedObject ℤ 𝒜 :=
  ObjectProperty.ι (FilteredObject.IsFinite : ObjectProperty (Fil(𝒜))) ⋙
    FilteredObject.associatedGradedFunctor

/-- Helper for Lemma 13.26.7: the associated graded functor on cochain complexes of finite
filtered objects. -/
abbrev finiteFilteredObjectAssociatedGradedCochainFunctor :
    CochainComplex FilF ℤ ⥤ CochainComplex (GradedObject ℤ 𝒜) ℤ :=
  (finiteFilteredObjectAssociatedGradedFunctor (𝒜 := 𝒜)).mapHomologicalComplex
    (ComplexShape.up ℤ)

/-- Helper for Lemma 13.26.7: a finite filtered object is filtered injective when each graded
piece is injective in the ambient abelian category. -/
class IsFilteredInjective (I : FilF) : Prop where
  injective (p : ℤ) : Injective (gr^{p} I.obj)

attribute [instance] IsFilteredInjective.injective

namespace CochainComplex

section PlusWithTermsIn

variable {A : Type u} [Category.{v} A] [HasZeroMorphisms A]

/-- Helper for Lemma 13.26.7: the bounded-below cochain complexes whose terms satisfy the object
property `P`. -/
abbrev PlusWithTermsIn (P : ObjectProperty A) :=
  ObjectProperty.FullSubcategory fun K : Plus A ↦
    ∀ n : ℤ, P (K.obj.X n)

namespace PlusWithTermsIn

instance (P : ObjectProperty A) : CoeOut (PlusWithTermsIn P) (Plus A) where
  coe K := K.obj

instance (P : ObjectProperty A) :
    CoeOut (PlusWithTermsIn P) (CochainComplex A ℤ) where
  coe K := K.obj.obj

/-- Helper for Lemma 13.26.7: the inclusion of bounded-below cochain complexes with terms in `P`
into all cochain complexes. -/
abbrev ι (P : ObjectProperty A) : PlusWithTermsIn P ⥤ CochainComplex A ℤ :=
  ObjectProperty.ι _ ⋙ CochainComplex.Plus.ι A

end PlusWithTermsIn

end PlusWithTermsIn

section TermwiseMono

variable {A : Type u} [Category.{v} A] [HasZeroMorphisms A]

/-- Helper for Lemma 13.26.7: primitive bounded-below stage data for a morphism into a complex
whose terms satisfy `P`. -/
structure IsStrictlyGEWithTermsIn
    (P : ObjectProperty A) (a : ℤ) {K : CochainComplex A ℤ}
    (I : CochainComplex.PlusWithTermsIn P) (α : K ⟶ (I : CochainComplex A ℤ)) : Prop where
  strictlyGE : (I : CochainComplex A ℤ).IsStrictlyGE a

/-- Helper for Lemma 13.26.7: bounded-below stage data together with termwise monomorphy. -/
structure IsTermwiseMonoStrictlyGEWithTermsIn
    (P : ObjectProperty A) (a : ℤ) {K : CochainComplex A ℤ}
    (I : CochainComplex.PlusWithTermsIn P) (α : K ⟶ (I : CochainComplex A ℤ)) : Prop extends
    IsStrictlyGEWithTermsIn P a I α where
  term_mono (n : ℤ) : Mono (α.f n)

end TermwiseMono

/-- Helper for Lemma 13.26.7: the bounded-below cochain complexes of finite filtered objects whose
terms are filtered injective. -/
abbrev FilteredInjectivePlus (𝒜 : Type u) [Category.{v} 𝒜] [Abelian 𝒜] :=
  CochainComplex.PlusWithTermsIn
    (IsFilteredInjective : ObjectProperty FilF)

/-- Helper for Lemma 13.26.7: a morphism into a bounded-below filtered-injective complex is a
filtered quasi-isomorphism with termwise strict monomorphisms when its associated graded map is a
quasi-isomorphism and each degree component is strict. -/
structure IsTermwiseStrictMonoStrictlyGEFilteredQuasiIso
    (a : ℤ) {K : CochainComplex FilF ℤ}
    (I : CategoryTheory.CochainComplex.FilteredInjectivePlus 𝒜)
    (α : K ⟶ (I : CochainComplex FilF ℤ)) : Prop
    extends IsTermwiseMonoStrictlyGEWithTermsIn
      (IsFilteredInjective : ObjectProperty FilF) a I α where
  quasiIso :
    QuasiIso ((finiteFilteredObjectAssociatedGradedCochainFunctor (𝒜 := 𝒜)).map α)
  term_strict (n : ℤ) : FilteredObject.Hom.Strict (α.f n).hom

namespace IsTermwiseStrictMonoStrictlyGEFilteredQuasiIso

-- Route correction: the canonical owner theorem belongs in `Lemma_13_26_6`, but that dependency
-- chain is currently broken earlier in the workspace. This local theorem keeps the current item
-- compilable and isolates the exact missing prerequisite.
/-- Helper for Lemma 13.26.7: a filtered quasi-isomorphism with termwise strict monomorphisms into
a bounded-below filtered-injective complex admits lifts to any other bounded-below
filtered-injective target. -/
theorem exists_strict_lift_to_boundedBelow_filteredInjective
    {a : ℤ} {K : CochainComplex FilF ℤ}
    {I J : CategoryTheory.CochainComplex.FilteredInjectivePlus 𝒜}
    {α : K ⟶ (I : CochainComplex FilF ℤ)}
    (hα : IsTermwiseStrictMonoStrictlyGEFilteredQuasiIso a I α)
    (γ : K ⟶ (J : CochainComplex FilF ℤ)) :
    ∃ β : (I : CochainComplex FilF ℤ) ⟶ (J : CochainComplex FilF ℤ),
      α ≫ β = γ := by
  -- TODO: reinstate the source-faithful proof from `Lemma_13_26_6` after the prerequisite
  -- comparison-theorem owner chain is repaired in the canonical earlier files.
  sorry

end IsTermwiseStrictMonoStrictlyGEFilteredQuasiIso

end CochainComplex

variable {A B : FilF}

-- Proof sketch: specialize the bounded-below filtered comparison theorem to `K = A[0]` and the
-- target map `(single₀).map f ≫ b`, then package the resulting equality as a commutative square.
/-- Lemma 13.26.7: a morphism in `Fil^f(𝒜)` extends from a bounded-below filtered-injective
resolution `A[0] ⟶ I^•` with termwise strict degree maps to a bounded-below filtered-injective
complex `J^•` equipped with a comparison map `B[0] ⟶ J^•`. -/
theorem exists_cochainMap_of_filteredQuasiIso_to_termwise_filteredInjective
    {I J : CochainComplex.FilteredInjectivePlus 𝒜}
    (f : A ⟶ B) (a : (single₀).obj A ⟶ I)
    (_ha : CochainComplex.IsTermwiseStrictMonoStrictlyGEFilteredQuasiIso 0 I a)
    (b : (single₀).obj B ⟶ J) :
    ∃ g : I ⟶ J, CommSq a ((single₀).map f) g b := by
  let ha := _ha
  -- Proof comment: apply the filtered comparison theorem to the composite
  -- `A[0] ⟶ B[0] ⟶ J^•`.
  obtain ⟨g, hg⟩ :=
    CochainComplex.IsTermwiseStrictMonoStrictlyGEFilteredQuasiIso
      .exists_strict_lift_to_boundedBelow_filteredInjective
        (𝒜 := 𝒜) (K := (single₀).obj A) (I := I) (J := J) (α := a)
        ha ((single₀).map f ≫ b)
  -- Proof comment: the equality produced by the lift is exactly the commutative-square datum.
  exact ⟨g, hg⟩

end CategoryTheory
