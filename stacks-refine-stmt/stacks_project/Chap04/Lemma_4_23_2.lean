import Mathlib.CategoryTheory.Limits.ExactFunctor
import Mathlib.CategoryTheory.Limits.Constructions.LimitsOfProductsAndEqualizers
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Terminal
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory

universe v₁ v₂ u₁ u₂

namespace CategoryTheory.Limits

variable {A : Type u₁} [Category.{v₁} A]
variable {B : Type u₂} [Category.{v₂} B]

/- Domain-style sampling for Lemma 4.23.2:
- primary domain: preservation of finite limits in category theory;
- sampled owner API:
  `leftExactFunctor`,
  `leftExactFunctor_iff`,
  `preservesFiniteLimits_of_preservesEqualizers_and_finiteProducts`,
  `preservesFiniteLimits_of_preservesTerminal_and_pullbacks`;
- best owner abstraction: the chapter's left-exactness owner `leftExactFunctor A B`;
- source/core/bridge triage:
  `source-facing`: the textbook decompositions of left exactness into
  products-plus-equalizers and terminal-object-plus-pullbacks;
  `core/canonical`: `leftExactFunctor A B`, with companion simplification
  `leftExactFunctor_iff`;
  `bridge/view`: the two equivalences below.

Primitive data here are the relevant shape-preservation assumptions. The finite-limit predicate is
derived API through `leftExactFunctor_iff`, so the file should stay a thin bridge to the canonical
mathlib theorems rather than introducing any parallel wrapper around left exactness. The auxiliary
conversion from terminal-object preservation to empty-diagram preservation is the standard bridge
`preservesLimitsOfShape_pempty_of_preservesTerminal`. -/

/- Companion recall: the converse directions are already owned by the canonical mathlib
constructors below. -/
recall preservesFiniteLimits_of_preservesEqualizers_and_finiteProducts
recall preservesFiniteLimits_of_preservesTerminal_and_pullbacks

/-- Lemma 4.23.2 (1): a functor is left exact if and only if it preserves finite products and
equalizers. -/
-- Proof sketch: one direction is immediate because finite products and equalizers are finite
-- limits. Conversely, use the canonical theorem
-- `preservesFiniteLimits_of_preservesEqualizers_and_finiteProducts`.
theorem leftExactFunctor_iff_preserves_finite_products_and_equalizers
    [HasEqualizers A] [HasFiniteProducts A] (F : A ⥤ B) :
    leftExactFunctor A B F ↔
      PreservesFiniteProducts F ∧ PreservesLimitsOfShape WalkingParallelPair F := by
  rw [leftExactFunctor_iff]
  constructor
  · intro hF
    letI := hF
    exact ⟨inferInstance, inferInstance⟩
  · rintro ⟨hprod, heq⟩
    letI := hprod
    letI := heq
    exact preservesFiniteLimits_of_preservesEqualizers_and_finiteProducts F

/-- Lemma 4.23.2 (2): a functor is left exact if and only if it preserves terminal objects and
pullbacks. -/
-- Proof sketch: one direction is immediate because terminal objects and pullbacks are finite
-- limits. Conversely, pass from preservation of the terminal object to preservation of the
-- `Discrete PEmpty`-shaped limits via `preservesLimitsOfShape_pempty_of_preservesTerminal`, then
-- apply the canonical theorem `preservesFiniteLimits_of_preservesTerminal_and_pullbacks`.
theorem leftExactFunctor_iff_preserves_terminal_and_pullbacks
    [HasTerminal A] [HasPullbacks A] (F : A ⥤ B) :
    leftExactFunctor A B F ↔
      PreservesLimit (Functor.empty.{0} A) F ∧ PreservesLimitsOfShape WalkingCospan F := by
  rw [leftExactFunctor_iff]
  constructor
  · intro hF
    letI := hF
    exact ⟨inferInstance, inferInstance⟩
  · rintro ⟨hterminal, hpullbacks⟩
    letI := hterminal
    letI := preservesLimitsOfShape_pempty_of_preservesTerminal F
    letI := hpullbacks
    exact preservesFiniteLimits_of_preservesTerminal_and_pullbacks F

end CategoryTheory.Limits
