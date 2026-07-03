import Mathlib
import Mathlib.Tactic.Recall
import StacksProject_2024.Chap13.Definition_13_18_1

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory

universe v u

namespace CochainComplex

section

variable {𝒜 : Type u} [Category.{v} 𝒜] [Abelian 𝒜]

/- Domain-style sampling for Lemma 13.31.4:
- primary domain: bounded-below injective cochain complexes and their K-injectivity;
- sampled owner declarations:
  `CochainComplex.InjectivePlus`,
  `CochainComplex.plus_iff`,
  `CochainComplex.isKInjective_of_injective`,
  `CochainComplex.PlusWithTermsIn.instIsKInjective`;
- best owner abstraction: the chapter owner `CochainComplex.InjectivePlus 𝒜` for bounded-below
  cochain complexes with injective terms;
- primitive data: an owner object `I : CochainComplex.InjectivePlus 𝒜`;
- derived API: the canonical `IsKInjective` instance recalled below.

Source/core/bridge triage:
- `source-facing`: the textbook formulation below for an arbitrary bounded-below cochain complex of
  injectives;
- `core/canonical`: `CochainComplex.InjectivePlus 𝒜` together with its `IsKInjective` instance;
- `bridge/view`: the source wording is already subsumed by the owner-level instance built from
  `CochainComplex.plus_iff` and `CochainComplex.isKInjective_of_injective`, so no separate bridge
  declaration is needed here.
-/

/- Lemma 13.31.4: in an abelian category, a bounded below cochain complex of injective objects is
K-injective. This is the canonical owner instance on `CochainComplex.InjectivePlus 𝒜`, recalled
here rather than redeclared under a parallel theorem name. -/
recall PlusWithTermsIn.instIsKInjective

end

end CochainComplex
