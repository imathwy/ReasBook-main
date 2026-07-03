import Mathlib
import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import Mathlib.CategoryTheory.Abelian.Subcategory
import StacksProject_2024.Chap12.Definition_12_10_1

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.ObjectProperty

universe u v

namespace CategoryTheory.GrothendieckTopology

variable {C : Type u} [Category.{v} C]
variable (τ τ' : GrothendieckTopology C)
variable [∀ X : C, HasInjectiveResolutions (Sheaf (τ'.over X) AddCommGrpCat.{max u v})]
variable [∀ {X Y : C} (f : X ⟶ Y),
  Functor.Additive
    ((Over.map f).sheafPushforwardCocontinuous AddCommGrpCat.{max u v} (τ'.over X) (τ'.over Y))]

/-- Situation 21.30.1: a comparison setup for cohomology on a category `C` with two
Grothendieck topologies `τ` and `τ'`, consisting of a morphism property `P` and for each object
`X` a weak LinearRepresentations_Serre_1977 subcategory `A'_X ⊂ Ab(C_{τ'}/X)`, such that `P` is stable under base change,
inverse image preserves the chosen subcategories, objects of `A'_X` are already `τ`-sheaves,
higher direct images along arrows in `P` stay in the chosen subcategories, and every `τ`-covering
admits the refinement pattern described in the text by `τ'`-coverings and singleton `P`-covers. -/
structure cohomology_comparison_situation
    (P : MorphismProperty C)
    (A' : ∀ X : C, ObjectProperty (Sheaf (τ'.over X) AddCommGrpCat.{max u v})) : Prop where
  /-- Each `A'_X` is a weak LinearRepresentations_Serre_1977 subcategory of `Ab(C_{τ'}/X)`. -/
  isWeakSerre : ∀ X : C, IsWeakSerreClass (A' X)
  /-- Base change of an arrow in `P` exists and again belongs to `P`. -/
  pullback_of_mem :
    ∀ ⦃X Y Y' : C⦄ (f : X ⟶ Y), P f → (g : Y' ⟶ Y) →
      ∃ (T : C) (p₁ : T ⟶ X) (p₂ : T ⟶ Y'),
        IsPullback p₁ p₂ f g ∧ P p₂
  /-- Inverse image along any morphism sends `A'_Y` into `A'_X`. -/
  inverseImage_mem :
    ∀ ⦃X Y : C⦄ (f : X ⟶ Y) ⦃ℱ : Sheaf (τ'.over Y) AddCommGrpCat.{max u v}⦄,
      A' Y ℱ → A' X ((τ'.overMapPullback AddCommGrpCat.{max u v} f).obj ℱ)
  /-- Every object of `A'_X` satisfies the sheaf condition for the coarser topology `τ`. -/
  isSheaf_for_coarser_topology :
    ∀ ⦃X : C⦄ ⦃ℱ : Sheaf (τ'.over X) AddCommGrpCat.{max u v}⦄,
      A' X ℱ → CategoryTheory.Presheaf.IsSheaf (τ.over X) ℱ.1
  /-- Higher direct images along arrows in `P` remain inside the chosen weak LinearRepresentations_Serre_1977
  subcategories. -/
  higherDirectImage_mem :
    ∀ ⦃X Y : C⦄ (f : X ⟶ Y), P f → ∀ (i : ℕ) ⦃ℱ : Sheaf (τ'.over X) AddCommGrpCat.{max u v}⦄,
      A' X ℱ →
        A' Y ((((Over.map f).sheafPushforwardCocontinuous AddCommGrpCat.{max u v}
          (τ'.over X) (τ'.over Y)).rightDerived i).obj ℱ)
  /-- Every `τ`-covering refines to a `τ'`-covering, followed by singleton covers from `P`, and
  then by further `τ'`-coverings as in the Stacks-project situation. -/
  tau_covering_refinement :
    ∀ ⦃U : C⦄ {ι : Type (max u v)} (cover : ι → Over U),
      (τ.over U).CoversTop cover →
        ∃ (J : Type (max u v)) (V : J → Over U),
          (τ'.over U).CoversTop V ∧
            ∃ (W : J → C) (f : ∀ j, W j ⟶ (V j).left),
              ∀ j,
                P (f j) ∧
                  Sieve.generate (Presieve.singleton (f j)) ∈ τ (V j).left ∧
                    ∃ (Kj : Type (max u v)) (Wcoverj : Kj → Over (W j)),
                      (τ'.over (W j)).CoversTop Wcoverj ∧
                        ∀ k : Kj,
                          ∃ i : ι,
                            Nonempty
                              ((Over.mk ((Wcoverj k).hom ≫ f j ≫ (V j).hom)) ⟶ cover i)

instance
    (h : cohomology_comparison_situation τ τ' P A') (X : C) :
    IsWeakSerreClass (A' X) :=
  h.isWeakSerre X

namespace cohomology_comparison_situation

/-- The pullback-existence part of a comparison situation induces the canonical owner
`P.HasPullbacks`. -/
theorem hasPullbacks
    (h : cohomology_comparison_situation τ τ' P A') :
    P.HasPullbacks where
  hasPullback {X Y S} {f : X ⟶ S} g hf := by
    obtain ⟨T, p₁, p₂, hpullback, _⟩ := h.pullback_of_mem f hf g
    exact hpullback.hasPullback

end cohomology_comparison_situation

end CategoryTheory.GrothendieckTopology
