import stacks_project.Chap04.Definition_4_33_9
import stacks_project.Chap08.Lemma_8_4_3_Fibered

open CategoryTheory
open CategoryTheory Functor
open Functor.IsPreFibered
open Functor.Fiber

universe u₁ u₂ v₁ v₂

section

variable {C : Type u₁} {X : Type u₂} [Category.{v₁} C] [Category.{v₂} X]
variable (J : GrothendieckTopology C) (p : X ⥤ C)
variable (P : ObjectProperty X)
variable [p.IsFibered]

section RestrictedFibered

variable [(P.ι ⋙ p).IsFibered]

/-- Helper for Lemma 8.4.3: the inclusion of the full subcategory is a based functor over the
same base category. -/
noncomputable def fullSubcategory_inclusion_basedFunctor :
    BasedCategory.ofFunctor (P.ι ⋙ p) ⥤ᵇ BasedCategory.ofFunctor p where
  toFunctor := P.ι
  w := rfl

/-- Helper for Lemma 8.4.3: the restricted projection viewed as a bundled fibred category over
`C`. -/
abbrev fullSubcategory_projection_fibredCategoryOver [h : (P.ι ⋙ p).IsFibered] :
    FibredCategoryOver C :=
  FibredCategoryOver.ofFunctor (P.ι ⋙ p)

/-- Helper for Lemma 8.4.3: the ambient projection viewed as a bundled fibred category over `C`. -/
abbrev ambient_projection_fibredCategoryOver : FibredCategoryOver C :=
  FibredCategoryOver.ofFunctor p

/-- Helper for Lemma 8.4.3: the inclusion based functor preserves strongly cartesian morphisms
from the restricted projection to the ambient projection. -/
lemma fullSubcategory_inclusion_preservesStronglyCartesian
    (hpullback : ∀ ⦃U V : C⦄ (f : V ⟶ U) (x : p.Fiber U) (_hx : P x.1),
      ((P.inverseImage (fiberInclusion : p.Fiber V ⥤ X)).isoClosure)
        (f ^*[canonicalPullbackChoice p] x))
    {a b : P.FullSubcategory} (φ : a ⟶ b)
    (hφ : (P.ι ⋙ p).IsStronglyCartesian ((P.ι ⋙ p).map φ) φ) :
    p.IsStronglyCartesian (p.map φ.hom) φ.hom := by
  -- The inclusion preserves strongly cartesian arrows because the restricted and ambient
  -- projections agree on the underlying morphism in `X`.
  letI : (P.ι ⋙ p).IsStronglyCartesian ((P.ι ⋙ p).map φ) φ := hφ
  exact
    fullSubcategory_hom_isStronglyCartesian_to_ambient
      (p := p) (P := P) hpullback
      (f := (P.ι ⋙ p).map φ) (φ := φ)

/-- Helper for Lemma 8.4.3: the inclusion based functor satisfies the owner-level strongly
cartesian preservation predicate needed to build the ambient fibred morphism. -/
lemma fullSubcategory_inclusion_basedFunctor_preservesStronglyCartesian
    (hpullback : ∀ ⦃U V : C⦄ (f : V ⟶ U) (x : p.Fiber U) (_hx : P x.1),
      ((P.inverseImage (fiberInclusion : p.Fiber V ⥤ X)).isoClosure)
        (f ^*[canonicalPullbackChoice p] x)) :
    (fullSubcategory_inclusion_basedFunctor (p := p) (P := P)).PreservesStronglyCartesian := by
  intro a b φ hφ
  -- The owner-level preservation predicate is the same ambient statement after forgetting the
  -- full-subcategory wrapper on morphisms.
  simpa using
    fullSubcategory_inclusion_preservesStronglyCartesian
      (p := p) (P := P) hpullback (φ := φ) hφ

/-- Helper for Lemma 8.4.3: the inclusion `P.ι` defines the single ambient fibred morphism used
throughout the remaining fixed-cover transport comparison. -/
noncomputable abbrev fullSubcategory_inclusion_fibredMor
    (J : GrothendieckTopology C)
    (hpullback : ∀ ⦃U V : C⦄ (f : V ⟶ U) (x : p.Fiber U) (_hx : P x.1),
      ((P.inverseImage (fiberInclusion : p.Fiber V ⥤ X)).isoClosure)
        (f ^*[canonicalPullbackChoice p] x)) :
    FibredCategoryOver.ofFunctor (P.ι ⋙ p) ⟶
      FibredCategoryOver.ofFunctor p :=
  -- Package the inclusion through the canonical owner constructor for fibred morphisms.
  FibredCategoryMor.ofBasedFunctor
    (fullSubcategory_inclusion_basedFunctor (p := p) (P := P))
    (fullSubcategory_inclusion_basedFunctor_preservesStronglyCartesian
      (p := p) (P := P) hpullback)

end RestrictedFibered

end
