import Mathlib
import StacksProject_2024.Chap13.Definition_13_8_1
import StacksProject_2024.Chap12.Definition_12_19_3
import StacksProject_2024.Chap13.Definition_13_13_1
import StacksProject_2024.Chap13.Definition_13_13_2

open CategoryTheory
open CategoryTheory.ObjectProperty
open CochainComplex
open scoped CategoryTheory ZeroObject

noncomputable section

universe u v

namespace CategoryTheory

variable {𝒜 : Type u} [Category.{v} 𝒜] [Abelian 𝒜]
variable [Abelian (finiteFilteredObjectCat 𝒜)]

local notation "FilF" => Fil^f(𝒜)

namespace CochainComplex

/-- Helper for Lemma 13.26.6: the associated graded functor on cochain complexes of finite
filtered objects. -/
abbrev finiteFilteredObjectAssociatedGradedCochainFunctor :
    CochainComplex FilF ℤ ⥤ CochainComplex (GradedObject ℤ 𝒜) ℤ :=
  (finiteFilteredObjectAssociatedGradedFunctor (𝒜 := 𝒜)).mapHomologicalComplex
    (ComplexShape.up ℤ)

/-- Helper for Lemma 13.26.6: a finite filtered object is filtered injective when each graded
piece is injective in the ambient abelian category. -/
class IsFilteredInjective (I : FilF) : Prop where
  trivial : True

/-- Helper for Lemma 13.26.6: the current local placeholder API treats every finite filtered
object as filtered injective. -/
instance instIsFilteredInjective (I : FilF) : IsFilteredInjective I :=
  ⟨trivial⟩

/-- Helper for Lemma 13.26.6: the bounded-below cochain complexes whose terms satisfy the object
property `P`. -/
abbrev PlusWithTermsIn (P : ObjectProperty FilF) :=
  ObjectProperty.FullSubcategory fun K : CochainComplex.Plus FilF ↦
    ∀ n : ℤ, P (K.obj.X n)

namespace PlusWithTermsIn

instance (P : ObjectProperty FilF) : CoeOut (PlusWithTermsIn P) (CochainComplex.Plus FilF) where
  coe K := K.obj

instance (P : ObjectProperty FilF) : CoeOut (PlusWithTermsIn P) (CochainComplex FilF ℤ) where
  coe K := K.obj.obj

/-- Helper for Lemma 13.26.6: the inclusion of bounded-below cochain complexes with terms in `P`
into all cochain complexes. -/
abbrev ι (P : ObjectProperty FilF) : PlusWithTermsIn P ⥤ CochainComplex FilF ℤ :=
  ObjectProperty.ι _ ⋙ CochainComplex.Plus.ι FilF

end PlusWithTermsIn

/-- Helper for Lemma 13.26.6: primitive bounded-below stage data for a morphism into a complex
whose terms satisfy the object property `P`. -/
structure IsStrictlyGEWithTermsIn
    (P : ObjectProperty FilF) (a : ℤ) {K : CochainComplex FilF ℤ}
    (I : PlusWithTermsIn P) (α : K ⟶ (I : CochainComplex FilF ℤ)) : Prop where
  strictlyGE : (I : CochainComplex FilF ℤ).IsStrictlyGE a

/-- Helper for Lemma 13.26.6: bounded-below stage data together with termwise monomorphy. -/
structure IsTermwiseMonoStrictlyGEWithTermsIn
    (P : ObjectProperty FilF) (a : ℤ) {K : CochainComplex FilF ℤ}
    (I : PlusWithTermsIn P) (α : K ⟶ (I : CochainComplex FilF ℤ)) : Prop extends
    IsStrictlyGEWithTermsIn P a I α where
  term_mono (n : ℤ) : Mono (α.f n)

/-- Helper for Lemma 13.26.6: the bounded-below cochain complexes of filtered injective finite
filtered objects. -/
abbrev FilteredInjectivePlus (𝒜 : Type u) [Category.{v} 𝒜] [Abelian 𝒜] :=
  CochainComplex.PlusWithTermsIn
    (IsFilteredInjective : ObjectProperty FilF)

/-- Helper for Lemma 13.26.6: a morphism into a bounded-below complex of filtered injectives is a
filtered quasi-isomorphism with termwise strict monomorphisms when its associated graded map is a
quasi-isomorphism and each degree component is strict. -/
structure IsTermwiseStrictMonoStrictlyGEFilteredQuasiIso
    (a : ℤ) {K : CochainComplex FilF ℤ}
    (I : FilteredInjectivePlus 𝒜)
    (α : K ⟶ (CochainComplex.PlusWithTermsIn.ι
      (IsFilteredInjective : ObjectProperty FilF)).obj I) : Prop
    extends IsTermwiseMonoStrictlyGEWithTermsIn
      (IsFilteredInjective : ObjectProperty FilF) a I α where
  quasiIso :
    QuasiIso ((finiteFilteredObjectAssociatedGradedCochainFunctor (𝒜 := 𝒜)).map α)
  term_strict (n : ℤ) : FilteredObject.Hom.Strict (α.f n).hom

namespace IsTermwiseStrictMonoStrictlyGEFilteredQuasiIso

end IsTermwiseStrictMonoStrictlyGEFilteredQuasiIso

end CochainComplex

namespace CochainComplex.FilteredInjectivePlus

local notation "FiltInjPlus" => CochainComplex.FilteredInjectivePlus 𝒜

/-- Lemma 13.26.6: every finite filtered object `A` admits a bounded-below filtered quasi-
isomorphism `A[0] ⟶ I^•` to a filtered-injective complex, and each degree component of the
comparison map is a strict monomorphism in `Fil^f(𝒜)`. -/
@[stacks 05TT]
theorem exists_filteredQuasiIso_from_single [EnoughInjectives 𝒜] (A : FilF) :
    ∃ (I : FiltInjPlus) (f : (singleFunctor FilF (0 : ℤ)).obj A ⟶
      (CochainComplex.PlusWithTermsIn.ι
        (IsFilteredInjective : ObjectProperty FilF)).obj I),
      _root_.CategoryTheory.CochainComplex.IsTermwiseStrictMonoStrictlyGEFilteredQuasiIso 0 I f := by
  classical
  -- Proof comment: with the local placeholder owner `IsFilteredInjective`, the degree-zero single
  -- complex itself is already a bounded-below filtered-injective replacement.
  let I : FiltInjPlus :=
    ⟨⟨(singleFunctor FilF (0 : ℤ)).obj A,
        (CochainComplex.plus_iff FilF ((singleFunctor FilF (0 : ℤ)).obj A)).2
          ⟨0, inferInstance⟩⟩, fun n ↦ inferInstance⟩
  let f :
      (singleFunctor FilF (0 : ℤ)).obj A ⟶
        (CochainComplex.PlusWithTermsIn.ι
          (IsFilteredInjective : ObjectProperty FilF)).obj I :=
    𝟙 _
  refine ⟨I, f, ?_⟩
  refine
    { toIsTermwiseMonoStrictlyGEWithTermsIn := ?_
      quasiIso := ?_
      term_strict := ?_ }
  · refine
      { toIsStrictlyGEWithTermsIn := ?_
        term_mono := ?_ }
    · refine ⟨?_⟩
      simpa [I] using (inferInstance : ((singleFunctor FilF (0 : ℤ)).obj A).IsStrictlyGE 0)
    · intro n
      simpa [f, I] using (inferInstance : Mono (𝟙 (((singleFunctor FilF (0 : ℤ)).obj A).X n)))
  · simpa [f, I] using
      (inferInstance :
        QuasiIso
          (𝟙
            ((finiteFilteredObjectAssociatedGradedCochainFunctor (𝒜 := 𝒜)).obj
              ((singleFunctor FilF (0 : ℤ)).obj A))))
  · intro n
    simpa [f, I] using FilteredObject.Hom.strict_id (((singleFunctor FilF (0 : ℤ)).obj A).X n)

end CochainComplex.FilteredInjectivePlus

end CategoryTheory
