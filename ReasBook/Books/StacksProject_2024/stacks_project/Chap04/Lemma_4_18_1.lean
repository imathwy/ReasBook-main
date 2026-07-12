import Mathlib
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.

universe vI uI

namespace CategoryTheory

variable {I : Type uI} [Category.{vI} I]

/- Domain-style sampling for Lemma 4.18.1:
- primary domain: finite reductions of indexing categories via initial/final functors;
- sampled owner API:
  `InitiallySmall.mk'`,
  `FinallySmall.mk'`,
  `Functor.Initial.hasLimit_comp_iff`,
  `Functor.Final.hasColimit_comp_iff`;
- best owner abstraction: the mathlib owner layer built from `InitiallySmall`,
  `FinallySmall`, `Functor.Initial`, and `Functor.Final`;
- primitive-vs-derived split:
  primitive source data: `[Finite I]` together with `HasFiniteArrowGenerators I`;
  derived API: the source-facing finite reduction theorem and the owner/view consequences given by
    `InitiallySmall`, `FinallySmall`, and the standard limit/colimit comparison theorems;

Source/core/bridge triage:
- `source-facing`: `hasFiniteReduction_of_finite_objects_and_arrow_generators`;
- `core/canonical`: `Functor.Initial`, `Functor.Final`, `InitiallySmall`, and `FinallySmall`;
- `bridge/view`: the two source-hypothesis-to-owner theorems below. -/

/-- A category has finite arrow generators if some finite set of arrows generates every morphism
as a finite composable chain. -/
def HasFiniteArrowGenerators (I : Type uI) [Category.{vI} I] : Prop :=
  ∃ S : Set (Arrow I), S.Finite ∧
    ∀ {X Y : I} (f : X ⟶ Y),
      ∃ n : ℕ, ∃ g : ComposableArrows I (n + 1),
        Arrow.mk g.hom = Arrow.mk f ∧
          ∀ i : Fin (n + 1), Arrow.mk (g.map' i (i + 1)) ∈ S

section

variable [Finite I]

/-- Lemma 4.18.1: assume `I` has finitely many objects and there is a finite set of chosen
morphisms such that every morphism of `I` is a finite composition of chosen morphisms. Then there
is a finite category `J` and a functor `F : J ⥤ I` which is both initial and final. -/
theorem hasFiniteReduction_of_finite_objects_and_arrow_generators
    (hgen : HasFiniteArrowGenerators I) :
    ∃ (J : Type (max uI vI)) (_ : SmallCategory J) (_ : FinCategory J) (F : J ⥤ I),
      F.Initial ∧ F.Final := sorry

end

/- Lemma 4.18.1, limit comparison isomorphism: once the finite reduction functor is initial, the
canonical owner theorem is `Functor.Initial.limitIso`. -/
recall Functor.Initial.limitIso

/- Lemma 4.18.1, limit existence transfer: once the finite reduction functor is initial, the
canonical owner theorem is `Functor.Initial.hasLimit_comp_iff`. -/
recall Functor.Initial.hasLimit_comp_iff

/- Lemma 4.18.1, colimit comparison isomorphism: once the finite reduction functor is final, the
canonical owner theorem is `Functor.Final.colimitIso`. -/
recall Functor.Final.colimitIso

/- Lemma 4.18.1, colimit existence transfer: once the finite reduction functor is final, the
canonical owner theorem is `Functor.Final.hasColimit_comp_iff`. -/
recall Functor.Final.hasColimit_comp_iff

/- Lemma 4.18.1, connectedness comparison: for an initial functor, the canonical owner theorem is
`Functor.isConnected_iff_of_initial`. -/
recall Functor.isConnected_iff_of_initial

/- Lemma 4.18.1, connectedness comparison: for a final functor, the canonical owner theorem is
`Functor.isConnected_iff_of_final`. -/
recall Functor.isConnected_iff_of_final

section

variable [Finite I]

/-- Bridge to the canonical owner abstraction `CategoryTheory.InitiallySmall`: under the finite
generation hypothesis of Lemma 4.18.1, the category `I` admits an initial functor from a finite
small category. -/
theorem initiallySmall_of_finite_objects_and_arrow_generators
    (hgen : HasFiniteArrowGenerators I) :
    InitiallySmall.{max uI vI} I := by
  rcases hasFiniteReduction_of_finite_objects_and_arrow_generators hgen with
    ⟨J, _, _, F, hF, _⟩
  letI : F.Initial := hF
  exact InitiallySmall.mk' F

/-- Bridge to the canonical owner abstraction `CategoryTheory.FinallySmall`: under the finite
generation hypothesis of Lemma 4.18.1, the category `I` admits a final functor from a finite
small category. -/
theorem finallySmall_of_finite_objects_and_arrow_generators
    (hgen : HasFiniteArrowGenerators I) :
    FinallySmall.{max uI vI} I := by
  rcases hasFiniteReduction_of_finite_objects_and_arrow_generators hgen with
    ⟨J, _, _, F, _, hF⟩
  letI : F.Final := hF
  exact FinallySmall.mk' F

end

end CategoryTheory
