import Mathlib
import StacksProject_2024.Chap13.Situation_13_15_1
import StacksProject_2024.Chap13.Lemma_13_14_14
import StacksProject_2024.Chap13.Lemma_13_20_1
import StacksProject_2024.Chap13.Lemma_13_20_2.Index

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open CategoryTheory
open CategoryTheory.MorphismProperty
open CategoryTheory.ObjectProperty
open ComplexShape
open DerivedCategory.TStructure
open scoped CategoryTheory

universe w v₁ v₂ u₁ u₂

attribute [local instance] HasDerivedCategory.standard

namespace CategoryTheory

section

variable {𝒜 : Type u₁} {𝒟 : Type u₂}
  [Category.{v₁} 𝒜] [Abelian 𝒜] [EnoughInjectives 𝒜]
  [Category.{v₂} 𝒟]

variable (F : K⁺(𝒜) ⥤ 𝒟)

/-- Helper for Lemma 13.20.2: the bounded-below homotopy objects whose terms are injective. -/
abbrev boundedBelowInjectiveHomotopyProperty (𝒜 : Type u₁)
    [Category.{v₁} 𝒜] [Abelian 𝒜] :
    ObjectProperty (K⁺(𝒜)) :=
  fun K ↦
    let C : CochainComplex 𝒜 ℤ := K.obj.as
    ∀ n : ℤ, Injective (C.X n)

local notation "QisPlus" => Qis⁺(𝒜)

attribute [local instance] mapBoundedBelowHomotopyToDerivedBelow_isLocalization

/-- Helper for Lemma 13.20.2: unpacking the object property gives termwise injectivity. -/
private lemma boundedBelowInjective_terms_injective
    (X : K⁺(𝒜)) (hX : boundedBelowInjectiveHomotopyProperty 𝒜 X) :
    ∀ n : ℤ, Injective (X.obj.as.X n) := by
  intro n
  -- Proof comment: the auxiliary object property is exactly the termwise injectivity condition.
  simpa [boundedBelowInjectiveHomotopyProperty] using hX n

/-- Helper for Lemma 13.20.2: package a bounded-below homotopy object with injective terms as a
bounded-below injective cochain complex. -/
private abbrev boundedBelowInjective_to_injectivePlus
    (X : K⁺(𝒜)) (hX : boundedBelowInjectiveHomotopyProperty 𝒜 X) :
    CochainComplex.InjectivePlus 𝒜 :=
  ⟨⟨X.obj.as, X.property⟩, boundedBelowInjective_terms_injective (𝒜 := 𝒜) X hX⟩

/-- Helper for Lemma 13.20.2: bounded-below homotopy objects with injective terms compute the
right derived functor of `F`. -/
lemma boundedBelowInjective_computesRightDerivedAt
    (X : K⁺(𝒜)) (hX : boundedBelowInjectiveHomotopyProperty 𝒜 X) :
    F.ComputesRightDerivedAt QisPlus X := by
  -- Proof comment: Lemma `13.20.1` already proves the injective-complex case, so only the
  -- packaging step from `X` to `CochainComplex.InjectivePlus 𝒜` remains here.
  simpa [boundedBelowInjective_to_injectivePlus] using
    (boundedBelowInjectiveComplex_computesRightDerivedFunctorAt
      (F := F)
      (boundedBelowInjective_to_injectivePlus (𝒜 := 𝒜) X hX))

/-- Helper for Lemma 13.20.2: each bounded-below complex should admit a quasi-isomorphism to a
bounded-below complex of injective objects that computes the right derived functor. -/
lemma exists_quasiIso_to_computesRightDerivedAt
    (X : K⁺(𝒜)) :
    ∃ (X' : K⁺(𝒜)) (s : X ⟶ X'),
      Qis⁺(𝒜) s ∧ F.ComputesRightDerivedAt (Qis⁺(𝒜)) X' := by
  -- Proof comment: use the bounded-below injective replacement from Lemma `13.18.3`, already
  -- packaged in the local helper module, and then invoke the previous computation lemma.
  rcases exists_quasiIso_to_boundedBelowInjective (𝒜 := 𝒜) X with ⟨X', s, hX', hs⟩
  refine ⟨X', s, ?_, ?_⟩
  · -- Proof comment: convert the underlying homotopy-category quasi-isomorphism to the bounded-
    -- below localization predicate.
    simpa [boundedBelowHomotopyQuasiIso] using hs
  · -- Proof comment: the replacement target computes because its terms are injective.
    exact boundedBelowInjective_computesRightDerivedAt (F := F) X' (by
      simpa [boundedBelowInjectiveHomotopyProperty] using hX')

-- Proof sketch: once each bounded-below complex reaches a bounded-below injective complex by a
-- quasi-isomorphism and computes the right derived functor there, Lemma 13.14.14 upgrades those
-- objectwise computation data to everywhere-definedness.
-- Lemma 13.14.14 upgrades those objectwise computation data to everywhere-definedness.
/-- Lemma 13.20.2: if `𝒜` is an abelian category with enough injectives, then for every exact
functor `F : K^+(\mathcal A) ⥤ \mathcal D` into a triangulated category, the right derived
functor `RF : D^+(\mathcal A) ⥤ \mathcal D` is everywhere defined. -/
theorem boundedBelow_hasPointwiseRightDerivedFunctor_of_enoughInjectives :
    F.HasPointwiseRightDerivedFunctor (Qis⁺(𝒜)) := by
  -- Proof comment: Lemma `13.14.14` globalizes the objectwise injective replacements constructed
  -- above.
  refine F.hasPointwiseRightDerivedFunctor_of_exists_computesRightDerivedAt QisPlus ?_
  intro X
  exact exists_quasiIso_to_computesRightDerivedAt (F := F) X

/-- Any functor out of `K^+(\mathcal A)` admits a bounded-below right derived functor when `𝒜`
has enough injectives. -/
instance boundedBelow_hasRightDerivedFunctor_of_enoughInjectives :
    F.HasRightDerivedFunctor (Qis⁺(𝒜)) := by
  let _ : F.HasPointwiseRightDerivedFunctor (Qis⁺(𝒜)) :=
    boundedBelow_hasPointwiseRightDerivedFunctor_of_enoughInjectives (F := F)
  infer_instance

end

section

variable {𝒜 : Type u₁} {ℬ : Type u₂}
  [Category.{v₁} 𝒜] [Category.{v₂} ℬ]
  [Abelian 𝒜] [EnoughInjectives 𝒜]
  [Abelian ℬ] [HasDerivedCategory.{w} ℬ]
  (F : 𝒜 ⥤ ℬ) [F.Additive]

-- Proof sketch: specialize the previous theorem to the canonical bounded-below source functor
-- `K^+(\mathcal A) ⥤ D^+(\mathcal B)` attached to `F`.
/-- An additive functor from an abelian category with enough injectives has its bounded-below
right derived functor to `D^+(\mathcal B)` everywhere defined. -/
theorem additiveFunctor_boundedBelow_hasPointwiseRightDerivedFunctor_of_enoughInjectives :
    (mapBoundedBelowHomotopyCategoryToDerivedBelow F).HasPointwiseRightDerivedFunctor
      (Qis⁺(𝒜)) := by
  -- Route correction: in the current Lean formalization the first half of Lemma `13.20.2`
  -- already applies to any bounded-below functor into a category, so the additive case is an
  -- immediate specialization.
  -- Proof comment: instantiate the first theorem with the canonical bounded-below functor
  -- associated to the additive functor `F`.
  simpa using
    (boundedBelow_hasPointwiseRightDerivedFunctor_of_enoughInjectives
      (𝒜 := 𝒜) (𝒟 := D⁺(ℬ))
      (F := mapBoundedBelowHomotopyCategoryToDerivedBelow F))

attribute [instance]
  additiveFunctor_boundedBelow_hasPointwiseRightDerivedFunctor_of_enoughInjectives

end

end CategoryTheory
