import Mathlib
import StacksProject_2024.Chap04.Definition_4_22_1
import StacksProject_2024.Chap04.Definition_4_27_20
import StacksProject_2024.Chap04.Remark_4_27_7
import StacksProject_2024.Chap04.Remark_4_27_15
import StacksProject_2024.Chap13.Lemma_13_5_8
import StacksProject_2024.Chap13.Lemma_13_14_14

open CategoryTheory.MorphismProperty
open CategoryTheory.ObjectProperty
open CategoryTheory.Limits

open scoped MorphismPropertyUnder MorphismPropertyOver

universe v₁ v₂ u₁ u₂

namespace CategoryTheory

namespace Functor

section

/- Domain-style sampling for Lemma 13.14.15:
- primary domain: pointwise derived-functor existence criteria from a source-facing subset of
  good objects for a localization class;
- inspected owner declarations:
  `Functor.ComputesRightDerivedAt`,
  `Functor.ComputesLeftDerivedAt`,
  `Functor.hasPointwiseRightDerivedFunctor_of_exists_computesRightDerivedAt`,
  `Functor.hasPointwiseLeftDerivedFunctor_of_exists_computesLeftDerivedAt`;
- best owner abstraction: the public API should live directly on the canonical derived-functor
  owner predicates above, with the subset hypotheses carried by `ObjectProperty D`.

Source/core/bridge triage:
- `source-facing`: the subset criteria from the Stacks proof;
- `core/canonical`: the derived-functor owner predicates
  `ComputesRightDerivedAt` / `ComputesLeftDerivedAt` and their pointwise-existence companions;
- `bridge/view`: the four theorems below, which translate the subset hypotheses into those owner
  predicates without introducing a second packaging layer.
-/

variable {D : Type u₁} {D' : Type u₂}
variable [Category.{v₁} D] [Category.{v₂} D']
variable (F : D ⥤ D') (S : MorphismProperty D)
variable [S.IsSaturatedMultiplicativeSystem]

section Right

variable (I : ObjectProperty D)

/-- Lemma 13.14.15 (2): under the subset criterion for right derived functors, any object of the
chosen good subset computes the right derived functor of `F` with respect to `S`. -/
theorem computesRightDerivedAt_of_mem_subset
    (hI_reaches : ∀ X : D, ∃ (X' : D) (s : X ⟶ X'), I X' ∧ S s)
    (hI_isIso :
      ∀ {X X' : D} (s : X ⟶ X'), I X → I X' → S s → IsIso (F.map s))
    {X : D} (hX : I X) :
    F.ComputesRightDerivedAt S X := by
  sorry

/-- Lemma 13.14.15 (1): if every object reaches an object of `I` by a denominator in `S`, and if
`F` inverts denominators between objects of `I`, then `F` has pointwise right derived functors
with respect to `S`. -/
theorem hasPointwiseRightDerivedFunctor_of_subset :
    (hI_reaches : ∀ X : D, ∃ (X' : D) (s : X ⟶ X'), I X' ∧ S s) →
    (hI_isIso :
      ∀ {X X' : D} (s : X ⟶ X'), I X → I X' → S s → IsIso (F.map s)) →
    F.HasPointwiseRightDerivedFunctor S :=
  fun hI_reaches hI_isIso ↦
    F.hasPointwiseRightDerivedFunctor_of_exists_computesRightDerivedAt S
      (fun X ↦ by
        rcases hI_reaches X with ⟨X', s, hX', hs⟩
        exact
          ⟨X', s, hs,
            computesRightDerivedAt_of_mem_subset F S I hI_reaches hI_isIso hX'⟩)

end Right

section Left

variable (P : ObjectProperty D)

/-- Lemma 13.14.15 (4): under the dual subset criterion, any object of the chosen good subset
computes the left derived functor of `F` with respect to `S`. -/
theorem computesLeftDerivedAt_of_mem_subset
    (hP_reaches : ∀ X : D, ∃ (X' : D) (s : X' ⟶ X), P X' ∧ S s)
    (hP_isIso :
      ∀ {X X' : D} (s : X ⟶ X'), P X → P X' → S s → IsIso (F.map s))
    {X : D} (hX : P X) :
    F.ComputesLeftDerivedAt S X := by
  sorry

/-- Lemma 13.14.15 (3): if every object receives a denominator in `S` from an object of `P`, and
if `F` inverts denominators between objects of `P`, then `F` has pointwise left derived functors
with respect to `S`. -/
theorem hasPointwiseLeftDerivedFunctor_of_subset :
    (hP_reaches : ∀ X : D, ∃ (X' : D) (s : X' ⟶ X), P X' ∧ S s) →
    (hP_isIso :
      ∀ {X X' : D} (s : X ⟶ X'), P X → P X' → S s → IsIso (F.map s)) →
    F.HasPointwiseLeftDerivedFunctor S :=
  fun hP_reaches hP_isIso ↦
    F.hasPointwiseLeftDerivedFunctor_of_exists_computesLeftDerivedAt S
      (fun X ↦ by
        rcases hP_reaches X with ⟨X', s, hX', hs⟩
        exact
          ⟨X', s, hs,
            computesLeftDerivedAt_of_mem_subset F S P hP_reaches hP_isIso hX'⟩)

end Left

end

end Functor

end CategoryTheory
