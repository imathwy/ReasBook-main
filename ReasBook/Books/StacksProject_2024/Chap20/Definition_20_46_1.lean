import Mathlib
import Mathlib.Tactic.Recall
import StacksProject_2024.Chap20.Lemma_20_47_9

noncomputable section

namespace AlgebraicGeometry.RingedSpace

/-
Domain-style sampling for Definition 20.46.1:
- primary domain: strictly perfect cochain complexes of module sheaves over a sheaf of rings, with
  the present item the ringed-space specialization;
- sampled owner declarations:
  `CochainComplex.IsStrictlyPerfect`,
  `cochainComplex_isStrictlyPerfect_iff`;
- best owner abstraction: the chapter-local owner `CochainComplex.IsStrictlyPerfect`, already
  defined generically for cochain complexes of module sheaves over a sheaf of rings;
- primitive data: strict lower and upper bounds together with the degreewise retract-of-finite-free
  presentation built into that owner;
- derived API: the source-facing bridge theorem `cochainComplex_isStrictlyPerfect_iff`.

Source/core/bridge triage:
- `source-facing`: Definition 20.46.1 itself, recalled here for complexes of `\mathcal O_X`-modules;
- `core/canonical`: `CochainComplex.IsStrictlyPerfect` from Lemma `20.47.9`;
- `bridge/view`: `cochainComplex_isStrictlyPerfect_iff`, which recovers the textbook boundedness
  plus explicit retract presentation.

The definition should therefore be a direct recall of the existing owner, not a second ringed-space
wrapper and not a parallel local predicate.
-/

/- Definition 20.46.1: the notion of a strictly perfect complex of `\mathcal O_X`-modules is the
existing owner `CochainComplex.IsStrictlyPerfect`. -/
recall CochainComplex.IsStrictlyPerfect

/- The source wording is recovered by the canonical bridge theorem, specialized to complexes of
`\mathcal O_X`-modules. -/
recall cochainComplex_isStrictlyPerfect_iff

end AlgebraicGeometry.RingedSpace
