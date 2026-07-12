import Mathlib
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open Abelian.DoldKan

universe v u

namespace CategoryTheory

variable {A : Type u} [Category.{v} A] [Abelian A]

/- Domain-style sampling for Lemma 14.24.1:
- primary domain: the Dold-Kan correspondence for simplicial objects in an abelian category and
  the normalized Moore complex functor;
- sampled owner declarations:
  `Abelian.DoldKan.N`,
  `Abelian.DoldKan.equivalence`,
  `Functor.ReflectsMonomorphisms`,
  `Functor.ReflectsEpimorphisms`;
- best owner abstraction: the canonical functor `N : SimplicialObject A ⥤ ChainComplex A ℕ`,
  viewed as the functor part of the Dold-Kan equivalence `Abelian.DoldKan.equivalence`;
- primitive data: only the ambient abelian category `A`;
- derived API: faithfulness and reflection of isomorphisms from the equivalence structure, and
  reflection of monomorphisms and epimorphisms from the canonical faithful-functor owners.

Source/core/bridge triage:
- `source-facing`: the four textbook clauses about the normalized Moore complex functor;
- `core/canonical`: `Abelian.DoldKan.equivalence` and its functor `N`;
- `bridge/view`: the generic functor-level instance machinery deriving reflected monos and epis
  from faithfulness.

This file therefore targets the `source-facing` layer by specializing already-canonical owner
facts, and should not keep parallel theorem wrappers around those exact instances.
-/

/- Companion recall: the normalized Moore complex functor is the functor of the canonical
Dold-Kan equivalence. -/
recall equivalence

/- Lemma 14.24.1 (1): for an abelian category `A`, the Dold-Kan normalized Moore complex functor
`N : SimplicialObject A ⥤ ChainComplex A ℕ` is faithful. -/
#check
  (show (N : SimplicialObject A ⥤ ChainComplex A ℕ).Faithful from by
    simpa using
      (inferInstance :
        ((equivalence : SimplicialObject A ≌ ChainComplex A ℕ).functor).Faithful))

/- Lemma 14.24.1 (2): for an abelian category `A`, the Dold-Kan normalized Moore complex functor
`N : SimplicialObject A ⥤ ChainComplex A ℕ` reflects isomorphisms. -/
#check
  (show Functor.ReflectsIsomorphisms (N : SimplicialObject A ⥤ ChainComplex A ℕ) from
    by
      simpa using
        (inferInstance :
          ((equivalence : SimplicialObject A ≌ ChainComplex A ℕ).functor).ReflectsIsomorphisms))

/- Lemma 14.24.1 (3): for an abelian category `A`, the Dold-Kan normalized Moore complex functor
`N : SimplicialObject A ⥤ ChainComplex A ℕ` reflects injections, i.e. monomorphisms. -/
#check
  (show Functor.ReflectsMonomorphisms (N : SimplicialObject A ⥤ ChainComplex A ℕ) from
    by
      simpa using
        (inferInstance :
          ((equivalence : SimplicialObject A ≌ ChainComplex A ℕ).functor).ReflectsMonomorphisms))

/- Lemma 14.24.1 (4): for an abelian category `A`, the Dold-Kan normalized Moore complex functor
`N : SimplicialObject A ⥤ ChainComplex A ℕ` reflects surjections, i.e. epimorphisms. -/
#check
  (show Functor.ReflectsEpimorphisms (N : SimplicialObject A ⥤ ChainComplex A ℕ) from
    by
      simpa using
        (inferInstance :
          ((equivalence : SimplicialObject A ≌ ChainComplex A ℕ).functor).ReflectsEpimorphisms))

end CategoryTheory
