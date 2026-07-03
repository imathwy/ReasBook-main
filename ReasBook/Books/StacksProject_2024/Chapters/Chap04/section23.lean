import Mathlib.CategoryTheory.Limits.Constructions.LimitsOfProductsAndEqualizers
import Mathlib.CategoryTheory.Limits.ExactFunctor
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Terminal
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Definition_4_23_1 (from Chap04) -/
universe v₁ v₂ u₁ u₂

namespace CategoryTheory

variable {C : Type u₁} [Category.{v₁} C]
variable {D : Type u₂} [Category.{v₂} D]

/- Source/core/bridge triage for Definition 4.23.1:
- primary domain: exactness predicates on functors, owned by
  `Mathlib/CategoryTheory/Limits/ExactFunctor`.
- inspected owner declarations: `leftExactFunctor`, `leftExactFunctor_iff`,
  `rightExactFunctor`, and `exactFunctor_iff`.
- best owner abstraction: the `ObjectProperty (C ⥤ D)` predicates
  `leftExactFunctor C D`, `rightExactFunctor C D`, and `exactFunctor C D`.
- layer: `core/canonical`; this numbered item is a direct recall of the owner predicates.
- primitive data: only the ambient categories `C` and `D`.
- derived API: bundled functor categories and `_iff` companion lemmas stay upstream; this file
  recalls only the canonical predicates used downstream.
-/

/- Definition 4.23.1 (1): the left-exact functors `C ⥤ D` form the canonical object property
`leftExactFunctor C D`, whose value on `F : C ⥤ D` is definitionally `PreservesFiniteLimits F`. -/
recall leftExactFunctor

/- Definition 4.23.1 (2): the right-exact functors `C ⥤ D` form the canonical object property
`rightExactFunctor C D`, whose value on `F : C ⥤ D` is definitionally
`PreservesFiniteColimits F`. -/
recall rightExactFunctor

/- Definition 4.23.1 (3): the exact functors `C ⥤ D` form the canonical object property
`exactFunctor C D`, whose value on `F : C ⥤ D` says that `F` is both left exact and right exact. -/
recall exactFunctor

/- Companion recall: exactness is definitionally preservation of finite limits together with
preservation of finite colimits. -/
recall exactFunctor_iff

end CategoryTheory

/-! ### Lemma_4_23_2 (from Chap04) -/
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

/-- Helper for Lemma 4.23.2: preserving a terminal object yields preservation of empty-diagram
limits. -/
lemma preserves_empty_limits_of_preserves_terminal (F : A ⥤ B)
    [PreservesLimit (Functor.empty.{0} A) F] :
    PreservesLimitsOfShape (Discrete PEmpty.{1}) F := by
  -- The empty diagram is the categorical encoding of terminal objects.
  exact preservesLimitsOfShape_pempty_of_preservesTerminal F

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
    -- A left exact functor preserves all finite limits, so the empty diagram and pullbacks
    -- are preserved by instance search.
    letI := hF
    exact ⟨inferInstance, inferInstance⟩
  · rintro ⟨hterminal, hpullbacks⟩
    -- Convert the terminal-object hypothesis into the empty-diagram instance expected by the
    -- canonical finite-limit constructor, then combine it with pullback preservation.
    letI := hterminal
    letI := preserves_empty_limits_of_preserves_terminal F
    letI := hpullbacks
    exact preservesFiniteLimits_of_preservesTerminal_and_pullbacks F

end CategoryTheory.Limits

/-! ### Lemma_4_23_3 (from Chap04) -/
open CategoryTheory

universe v₁ v₂ u₁ u₂

namespace CategoryTheory.Limits

/- Domain-style sampling for Lemma 4.23.3:
- primary domain: right exactness and finite-colimit preservation in category theory;
- sampled owner API:
  `rightExactFunctor`,
  `rightExactFunctor_iff`,
  `preservesFiniteColimits_of_preservesCoequalizers_and_finiteCoproducts`,
  `preservesFiniteColimits_of_preservesInitial_and_pushouts`,
  `preservesColimitsOfShape_pempty_of_preservesInitial`;
- best owner abstraction: the chapter's right-exactness owner `rightExactFunctor C D`;
- source/core/bridge triage:
  `source-facing`: the textbook decompositions of right exactness into
  coproducts-plus-coequalizers and initial-object-plus-pushouts;
  `core/canonical`: `rightExactFunctor C D`, with companion simplification
  `rightExactFunctor_iff`;
  `bridge/view`: the two equivalences below.

Primitive data here are the relevant shape-preservation assumptions. The finite-colimit predicate is
derived API through `rightExactFunctor_iff`, so this file should stay a thin bridge to the
canonical mathlib constructors rather than keeping a parallel public surface phrased directly in
`PreservesFiniteColimits`. -/

variable {C : Type u₁} [Category.{v₁} C]
variable {D : Type u₂} [Category.{v₂} D]

/- Companion recall: the converse directions are already owned by the canonical mathlib
constructors below. -/
recall preservesFiniteColimits_of_preservesCoequalizers_and_finiteCoproducts
recall preservesFiniteColimits_of_preservesInitial_and_pushouts

/-- Lemma 4.23.3 (1): a functor is right exact if and only if it preserves finite coproducts and
coequalizers. -/
-- Proof sketch: one direction is immediate because finite coproducts and coequalizers are finite
-- colimits. Conversely, use
-- `preservesFiniteColimits_of_preservesCoequalizers_and_finiteCoproducts`.
theorem rightExactFunctor_iff_preserves_finite_coproducts_and_coequalizers
    [HasCoequalizers C] [HasFiniteCoproducts C] (F : C ⥤ D) :
    rightExactFunctor C D F ↔
      PreservesFiniteCoproducts F ∧ PreservesColimitsOfShape WalkingParallelPair F := by
  rw [rightExactFunctor_iff]
  constructor
  · intro hF
    letI := hF
    exact ⟨inferInstance, inferInstance⟩
  · rintro ⟨hcoprod, hcoeq⟩
    letI := hcoprod
    letI := hcoeq
    exact preservesFiniteColimits_of_preservesCoequalizers_and_finiteCoproducts F

/-- Lemma 4.23.3 (2): a functor is right exact if and only if it preserves initial objects and
pushouts. -/
-- Proof sketch: one direction is immediate because initial objects and pushouts are finite
-- colimits. Conversely, pass from preservation of the initial object to preservation of
-- `Discrete PEmpty`-shaped colimits via `preservesColimitsOfShape_pempty_of_preservesInitial`,
-- then apply `preservesFiniteColimits_of_preservesInitial_and_pushouts`.
theorem rightExactFunctor_iff_preserves_initial_and_pushouts
    [HasInitial C] [HasPushouts C] (F : C ⥤ D) :
    rightExactFunctor C D F ↔
      PreservesColimit (Functor.empty.{0} C) F ∧ PreservesColimitsOfShape WalkingSpan F := by
  rw [rightExactFunctor_iff]
  constructor
  · intro hF
    letI := hF
    exact ⟨inferInstance, inferInstance⟩
  · rintro ⟨hinitial, hpushouts⟩
    letI : PreservesColimit (Functor.empty.{0} C) F := hinitial
    letI : PreservesColimitsOfShape (Discrete PEmpty) F :=
      preservesColimitsOfShape_pempty_of_preservesInitial F
    letI := hpushouts
    exact preservesFiniteColimits_of_preservesInitial_and_pushouts F

end CategoryTheory.Limits
