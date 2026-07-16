import stacks_proof.stacks_project.Chap12.Definition_12_5_3
import Mathlib.CategoryTheory.Balanced
import Mathlib.Tactic.Recall
import Mathlib.Tactic.StacksAttribute

-- Declarations for this item will be appended below by the statement pipeline.

universe v u

namespace CategoryTheory

open Limits

/- 
Domain-style sampling for Lemma 12.5.4:
- primary domain: the source-facing injective/surjective/isomorphism criteria for morphisms in a
  preadditive balanced category;
- inspected owner declarations:
  `IsInjective`,
  `IsSurjective`,
  `isInjective_iff_mono`,
  `isSurjective_iff_epi`,
  `isIso_iff_mono_and_epi`,
  together with the source-facing vocabulary from Definition `12.5.3`;
- best owner abstraction: the chapter owner predicates `IsInjective f` and `IsSurjective f`,
  bridged to the categorical predicates `Mono f`, `Epi f`, and `IsIso f`;
- primitive data: a morphism `f : X ⟶ Y`;
- derived API: the equivalences `isInjective_iff_mono` and `isSurjective_iff_epi`, together with
  the source-facing criterion combining them for isomorphisms.

Source/core/bridge triage:
- `source-facing`: the textbook predicates `IsInjective f` and `IsSurjective f` from Definition
  `12.5.3`, and the criterion that an isomorphism is exactly a morphism that is both injective and
  surjective;
- `core/canonical`: `Mono f`, `Epi f`, and `IsIso f`;
- `bridge/view`: `isInjective_iff_mono`, `isSurjective_iff_epi`, and `isIso_iff_mono_and_epi`.
-/

section MonoCriterion

variable {C : Type u} [Category.{v} C] [Preadditive C]
variable {X Y : C} (f : X ⟶ Y) [HasKernel f]

/- Lemma 12.5.4 (1): the source-facing injective condition from Definition `12.5.3` is equivalent
to the owner predicate `Mono f`. -/
recall isInjective_iff_mono

end MonoCriterion

section EpiCriterion

variable {C : Type u} [Category.{v} C] [Preadditive C]
variable {X Y : C} (f : X ⟶ Y) [HasCokernel f]

/- Lemma 12.5.4 (2): dually, the source-facing surjective condition from Definition `12.5.3` is
equivalent to the owner predicate `Epi f`. -/
recall isSurjective_iff_epi

end EpiCriterion

section

variable {C : Type u} [Category.{v} C] [Preadditive C] [Balanced C]
variable {X Y : C} (f : X ⟶ Y) [HasKernel f] [HasCokernel f]

/-
Lemma 12.5.4 (3): the canonical owner theorem for the isomorphism criterion in a balanced
category is `isIso_iff_mono_and_epi`.
-/
recall isIso_iff_mono_and_epi

/-- Lemma 12.5.4 (3): a morphism is an isomorphism exactly when it is both injective and
surjective, in the source-facing sense of Definition `12.5.3`. -/
@[stacks 010C]
theorem isIso_iff_isInjective_and_isSurjective :
    IsIso f ↔ IsInjective f ∧ IsSurjective f := by
  rw [isIso_iff_mono_and_epi, ← isInjective_iff_mono f, ← isSurjective_iff_epi f]

end

end CategoryTheory
