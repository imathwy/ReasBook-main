import Mathlib
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.

universe v u

namespace CategoryTheory.Abelian.DoldKan

variable {A : Type u} [Category.{v} A] [Abelian A]

/- Domain-style sampling for Theorem 14.24.3:
- primary domain: the Dold-Kan correspondence for simplicial objects in an abelian category and
  the normalized Moore complex functor;
- sampled owner declarations:
  `CategoryTheory.Abelian.DoldKan.N`,
  `CategoryTheory.Abelian.DoldKan.Γ`,
  `CategoryTheory.Abelian.DoldKan.equivalence`,
  `CategoryTheory.Idempotents.DoldKan.equivalence`;
- best owner abstraction: the canonical owner is
  `CategoryTheory.Abelian.DoldKan.equivalence : SimplicialObject A ≌ ChainComplex A ℕ`, whose
  functor is definitionally the normalized Moore complex `N`;
- primitive data: the ambient abelian category `A`;
- derived API: the specific functors `N`, `Γ`, and the induced equivalence itself.

Source/core/bridge triage:
- `source-facing`: the theorem that the normalized Moore complex functor induces the Dold-Kan
  equivalence;
- `core/canonical`: `equivalence`;
- `bridge/view`: the comparison with the pseudoabelian construction used internally upstream. -/

/- Theorem 14.24.3: the normalized Moore complex functor
`CategoryTheory.Abelian.DoldKan.N : SimplicialObject A ⥤ ChainComplex A ℕ`
induces the Dold-Kan equivalence
`SimplicialObject A ≌ ChainComplex A ℕ`. -/
recall equivalence

end CategoryTheory.Abelian.DoldKan
