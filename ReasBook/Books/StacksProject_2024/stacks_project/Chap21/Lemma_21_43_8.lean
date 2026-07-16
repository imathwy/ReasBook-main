import StacksProject_2024.stacks_project.Chap13.Lemma_13_39_1
import StacksProject_2024.stacks_project.Chap21.Aux_21_43_1
import StacksProject_2024.stacks_project.Chap21.Lemma_21_43_7

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.ObjectProperty
open Opposite

attribute [local instance] HasDerivedCategory.standard

universe u v

namespace CategoryTheory.ModulesOnCategory

section

/-
Domain-style sampling:
- primary domain: Brown-representability input data for a full subcategory of a triangulated
  category, specialized to the `κ`-bounded objects of `QC(\mathcal O)`;
- sampled owner declarations:
  `CategoryTheory.IsBrownRepresentabilitySet`,
  `CategoryTheory.ModulesOnCategory.QC`,
  `CategoryTheory.ModulesOnCategory.derivedObjectCardinal`,
  `CategoryTheory.ObjectProperty.FullSubcategory`;
- best owner abstraction: the set of `κ`-bounded objects in `QC(\mathcal O)`, with
  `IsBrownRepresentabilitySet` as the canonical Chapter `13` owner once the ambient triangulated
  and coproduct structure is available;
- primitive data: the cardinal `κ` and the size invariant `derivedObjectCardinal`;
- derived API: nonzero detection and countable-coproduct factorization for that bounded-object
  set, together with the bridge to `IsBrownRepresentabilitySet`.

Source/core/bridge triage:
- `source-facing`: the existence of a cardinal `κ` controlling bounded nonzero sources and
  countable coproduct factorizations;
- `core/canonical`: `IsBrownRepresentabilitySet` for a set of objects in a triangulated category;
- `bridge/view`: `boundedObjects_isBrownRepresentabilitySet`, which turns the source-facing
  `κ`-bounded clauses into the canonical Brown-set owner. -/

variable {C : Type u} [Category.{v} C]
variable (𝒪 : Cᵒᵖ ⥤ CommRingCat.{u})
variable
  (RGamma :
    ∀ U : C,
      DerivedCategory (PresheafOfModules (𝒪 ⋙ forget₂ CommRingCat RingCat)) ⥤
        DerivedCategory (ModuleCat (𝒪.obj (op U))))
variable
  (derivedRestrict :
    ∀ {U V : C},
      (U ⟶ V) →
        DerivedCategory (ModuleCat (𝒪.obj (op V))) ⥤
          DerivedCategory (ModuleCat (𝒪.obj (op U))))
variable
  (comparison :
    ∀ {U V : C} (f : U ⟶ V),
      RGamma V ⋙ derivedRestrict f ⟶ RGamma U)

local notation "Ring𝒪" => 𝒪 ⋙ forget₂ CommRingCat RingCat
local notation "DModO" => DerivedCategory (PresheafOfModules Ring𝒪)

local notation "QCoh" => QC 𝒪 RGamma derivedRestrict comparison
open scoped ModulesOnCategoryCardinal

/-- The set of `κ`-bounded quasi-coherent objects. -/
def boundedObjects (κ : Cardinal) : Set QCoh :=
  fun E ↦ sizeD[Ring𝒪](E.obj) ≤ κ

/-- The first source-facing clause of Lemma `21.43.8`: every nonzero object of `QC(𝒪)` receives
a nonzero map from a `κ`-bounded object. -/
def boundedObjectsDetectsNonzeroObjects (κ : Cardinal) : Prop :=
  ∀ (K : QCoh), ¬ IsZero K →
    ∃ (E : QCoh), E ∈ boundedObjects 𝒪 RGamma derivedRestrict comparison κ ∧
      ∃ f : E ⟶ K, f ≠ 0

/-- The second source-facing clause of Lemma `21.43.8`: every map from a `κ`-bounded object into
a countable coproduct factors through a countable coproduct of `κ`-bounded source objects. -/
def boundedObjectsFactorThroughCountableCoproducts (κ : Cardinal) : Prop :=
  ∀ ⦃E : QCoh⦄,
    E ∈ boundedObjects 𝒪 RGamma derivedRestrict comparison κ →
      ∀ (K : ℕ → QCoh) [HasCoproduct K] (α : E ⟶ ∐ K),
        ∃ (E' : ℕ → QCoh) (_ : HasCoproduct E')
          (φ : ∀ n : ℕ, E' n ⟶ K n) (β : E ⟶ ∐ E'),
          (∀ n : ℕ, E' n ∈ boundedObjects 𝒪 RGamma derivedRestrict comparison κ) ∧
            α = β ≫ Limits.Sigma.map φ

/-- The source-facing boundedness clauses of Lemma `21.43.8` induce the canonical Brown
representability owner on the set of `κ`-bounded quasi-coherent objects. -/
theorem boundedObjects_isBrownRepresentabilitySet
    [HasZeroObject QCoh] [HasShift QCoh ℤ]
    [∀ n : ℤ, (shiftFunctor QCoh n).Additive]
    [Pretriangulated QCoh] [IsTriangulated QCoh] [HasCoproducts QCoh]
    {κ : Cardinal}
    (hsmall : boundedObjectsDetectsNonzeroObjects 𝒪 RGamma derivedRestrict comparison κ)
    (hfactor : boundedObjectsFactorThroughCountableCoproducts
      𝒪 RGamma derivedRestrict comparison κ) :
    IsBrownRepresentabilitySet (boundedObjects 𝒪 RGamma derivedRestrict comparison κ) := by
  refine ⟨?_, ?_⟩
  · intro K hK
    exact hsmall K hK
  · intro K E hE α
    rcases hfactor hE K α with ⟨E', hE', φ, β, hbounded, hα⟩
    let _ : HasCoproduct E' := hE'
    refine ⟨E', hbounded, φ, β, ?_⟩
    simpa using hα.symm

-- Proof sketch: choose `κ` dominating the bounds from Lemmas `21.43.6`, `21.43.7`, and
-- `15.103.5`. For a nonzero `K`, represent a nonzero cohomology class by a small image subcomplex
-- and enlarge it using the quasi-coherent closure construction to obtain a nonzero bounded source.
-- For a map into a countable coproduct, represent it on complexes, factor each component through a
-- bounded quasi-coherent subcomplex, and reassemble these componentwise factorizations into a map
-- through the coproduct of the bounded sources.
/-- Lemma 21.43.8: there exists a cardinal `κ` such that every nonzero object of `QC(𝒪)`
receives a nonzero morphism from a `κ`-bounded object, and every morphism from a `κ`-bounded
object into a countable direct sum factors through a countable direct sum of `κ`-bounded source
objects. -/
@[stacks 0GYZ]
theorem exists_cardinal_for_small_sources_and_countable_coproduct_factorizations :
    ∃ κ : Cardinal,
      boundedObjectsDetectsNonzeroObjects 𝒪 RGamma derivedRestrict comparison κ ∧
        boundedObjectsFactorThroughCountableCoproducts
          𝒪 RGamma derivedRestrict comparison κ := sorry

/-- Companion bridge for Lemma `21.43.8`: there is a cardinal `κ` for which the set of
`κ`-bounded quasi-coherent objects is itself a Brown representability set. -/
theorem exists_cardinal_for_boundedObjects_isBrownRepresentabilitySet
    [HasZeroObject QCoh] [HasShift QCoh ℤ]
    [∀ n : ℤ, (shiftFunctor QCoh n).Additive]
    [Pretriangulated QCoh] [IsTriangulated QCoh] [HasCoproducts QCoh] :
    ∃ κ : Cardinal,
      IsBrownRepresentabilitySet (boundedObjects 𝒪 RGamma derivedRestrict comparison κ) := by
  rcases exists_cardinal_for_small_sources_and_countable_coproduct_factorizations
      𝒪 RGamma derivedRestrict comparison with
    ⟨κ, hsmall, hfactor⟩
  exact ⟨κ, boundedObjects_isBrownRepresentabilitySet
    𝒪 RGamma derivedRestrict comparison hsmall hfactor⟩

/-- Companion bridge for Lemma `21.43.8`: the quasi-coherent subcategory `QC(𝒪)` satisfies the
Brown representability-set hypothesis from Chapter `13`. -/
theorem qc_exists_brownRepresentabilitySet
    [HasZeroObject QCoh] [HasShift QCoh ℤ]
    [∀ n : ℤ, (shiftFunctor QCoh n).Additive]
    [Pretriangulated QCoh] [IsTriangulated QCoh] [HasCoproducts QCoh] :
    ∃ S : Set QCoh, IsBrownRepresentabilitySet S := by
  rcases exists_cardinal_for_boundedObjects_isBrownRepresentabilitySet
      𝒪 RGamma derivedRestrict comparison with
    ⟨κ, hκ⟩
  exact ⟨boundedObjects 𝒪 RGamma derivedRestrict comparison κ, hκ⟩

end

end CategoryTheory.ModulesOnCategory
