import Mathlib
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.

namespace CategoryTheory

/- Domain-style sampling for Lemma 12.5.14:
- primary domain: stability of epimorphisms and monomorphisms under pullback and pushout in an
  abelian category;
- inspected owner declarations:
  `Abelian.epi_pullback_of_epi_f`,
  `Abelian.epi_pullback_of_epi_g`,
  `Abelian.mono_pushout_of_mono_f`,
  `Abelian.mono_pushout_of_mono_g`;
- best owner abstraction: the categorical owner predicates `Epi` and `Mono`, with the canonical
  stability results already owned by `CategoryTheory.Abelian`;
- primitive data: a pullback or pushout square together with an epic or monic edge;
- derived API: the induced epic or monic structure on the opposite projection or inclusion.

Source/core/bridge triage:
- `source-facing`: the textbook statements that surjections stay surjective after pullback and
  injections stay injective after pushout;
- `core/canonical`: the owner instances `Epi (pullback.snd f g)` and
  `Mono (pushout.inr f g : Z ⟶ pushout f g)`;
- `bridge/view`: this file is recall-only, so it should use the upstream owners directly rather
  than restating their full interfaces locally.
-/

/- Lemma 12.5.14 (1): in an abelian category, if `x ⟶ y` is surjective, then for every
`z ⟶ y` the projection `x ×_y z ⟶ z` is surjective. This is the canonical abelian-category
statement that pullbacks preserve epimorphisms. -/
recall Abelian.epi_pullback_of_epi_f

/- Lemma 12.5.14 (2): in an abelian category, if `x ⟶ y` is injective, then for every
`x ⟶ z` the canonical morphism `z ⟶ z ⨿_x y` is injective. This is the canonical
abelian-category statement that pushouts preserve monomorphisms. -/
recall Abelian.mono_pushout_of_mono_f

end CategoryTheory
