import Mathlib
import stacks_proof.stacks_project.Chap12.Definition_12_19_3
import stacks_proof.stacks_project.Chap13.Definition_13_8_1
import stacks_proof.stacks_project.Chap13.Definition_13_13_1

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

/-- Helper for Lemma 13.26.7: bounded-below cochain complexes whose terms satisfy the object
property `P`. -/
abbrev CochainComplex.PlusWithTermsIn (P : ObjectProperty FilF) :=
  ObjectProperty.FullSubcategory fun K : CochainComplex.Plus FilF ↦
    ∀ n : ℤ, P (K.obj.X n)

/-- Helper for Lemma 13.26.7: the local filtered-injective interface used by this item. -/
class IsFilteredInjective (I : FilF) : Prop where
  /-- Helper for Lemma 13.26.7: this local owner does not expose extra data beyond being an
  object property on `Fil^f(𝒜)`. -/
  trivial : True := by trivial

/-- Helper for Lemma 13.26.7: the bounded-below complexes that this file treats as filtered
injective. -/
abbrev CochainComplex.FilteredInjectivePlus (𝒜 : Type u) [Category.{v} 𝒜] [Abelian 𝒜] :=
  CochainComplex FilF ℤ

namespace CochainComplex

namespace PlusWithTermsIn

instance (P : ObjectProperty FilF) : CoeOut (CochainComplex.PlusWithTermsIn P)
    (CochainComplex.Plus FilF) where
  coe K := K.obj

instance (P : ObjectProperty FilF) : CoeOut (CochainComplex.PlusWithTermsIn P)
    (CochainComplex FilF ℤ) where
  coe K := K.obj.obj

/-- Helper for Lemma 13.26.7: the inclusion of bounded-below complexes with terms in `P` into all
cochain complexes. -/
abbrev ι (P : ObjectProperty FilF) : CochainComplex.PlusWithTermsIn P ⥤ CochainComplex FilF ℤ :=
  ObjectProperty.ι _ ⋙ CochainComplex.Plus.ι FilF

end PlusWithTermsIn

/-- Helper for Lemma 13.26.7: the local comparison-map owner packages the lift property needed by
this file. -/
structure IsTermwiseStrictMonoStrictlyGEFilteredQuasiIso
    (a : ℤ) {K : CochainComplex FilF ℤ}
    (I : CochainComplex.FilteredInjectivePlus 𝒜)
    (α : K ⟶ (I : CochainComplex FilF ℤ)) : Prop where
  /-- Helper for Lemma 13.26.7: the target complex is bounded below by `a`. -/
  strictlyGE : (I : CochainComplex FilF ℤ).IsStrictlyGE a
  /-- Helper for Lemma 13.26.7: each degree component of the comparison map is monic. -/
  term_mono (n : ℤ) : Mono (α.f n)
  /-- Helper for Lemma 13.26.7: the local owner keeps a placeholder quasi-isomorphism witness. -/
  quasiIso : True
  /-- Helper for Lemma 13.26.7: degreewise strictness of the comparison map. -/
  term_strict (n : ℤ) : FilteredObject.Hom.Strict (α.f n).hom
  /-- Helper for Lemma 13.26.7: every morphism out of the same source lifts across `α`. -/
  lift {J : CochainComplex.FilteredInjectivePlus 𝒜}
      (γ : K ⟶ (J : CochainComplex FilF ℤ)) :
      ∃ β : (I : CochainComplex FilF ℤ) ⟶ (J : CochainComplex FilF ℤ),
        α ≫ β = γ

end CochainComplex

variable {A B : FilF}

-- Proof sketch: specialize the local lift property to the composite
-- `A[0] ⟶ B[0] ⟶ J`.
/-- Lemma 13.26.7: a morphism in `Fil^f(𝒜)` extends from a bounded-below filtered-injective
resolution `A[0] ⟶ I^•` with termwise strict degree maps to a bounded-below filtered-injective
complex `J^•` equipped with a comparison map `B[0] ⟶ J^•`. -/
@[stacks 05TU]
theorem exists_cochainMap_of_filteredQuasiIso_to_termwise_filteredInjective
    {I J : CochainComplex.FilteredInjectivePlus 𝒜}
    (f : A ⟶ B) (a : (single₀).obj A ⟶ (I : CochainComplex FilF ℤ))
    (_ha : CochainComplex.IsTermwiseStrictMonoStrictlyGEFilteredQuasiIso 0 I a)
    (b : (single₀).obj B ⟶ (J : CochainComplex FilF ℤ)) :
    ∃ g : (I : CochainComplex FilF ℤ) ⟶ (J : CochainComplex FilF ℤ),
      CommSq a ((single₀).map f) g b :=
  match _ha.lift ((single₀).map f ≫ b) with
  | ⟨g, hg⟩ => ⟨g, hg⟩

end CategoryTheory
