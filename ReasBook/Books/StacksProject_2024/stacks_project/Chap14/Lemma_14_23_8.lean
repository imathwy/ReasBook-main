import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open Abelian.DoldKan

universe v u

namespace CategoryTheory

section

variable {A : Type u} [Category.{v} A] [Abelian A]

/- Domain-style sampling for Lemma 14.23.8:
- primary domain: exact functors in the Dold-Kan equivalence between simplicial objects and chain
  complexes of an abelian category;
- sampled owner declarations:
  `exactFunctor`,
  `ExactFunctor.of`,
  `N`,
  `equivalence`;
- best owner abstraction: the canonical bundled exact functor
  `ExactFunctor.of (equivalence.functor : SimplicialObject A ⥤ ChainComplex A ℕ)`;
- primitive data: the ambient abelian category `A`;
- derived API: the source-facing exactness theorem for the normalized Moore complex functor.

Source/core/bridge triage:
- `source-facing`: the Stacks statement that the normalized Moore complex functor `N` is exact;
- `core/canonical`: the bundled exact functor `ExactFunctor.of equivalence.functor`;
- `bridge/view`: this theorem takes the property field of that canonical owner and transports it to
  `N` via the definitional equality built into `Abelian.DoldKan.equivalence`, so no parallel local
  exactness wrapper is needed. -/

-- Proof sketch: the Dold-Kan equivalence functor is exact by the canonical owner
-- `ExactFunctor.of equivalence.functor`, since equivalence functors preserve finite limits and
-- finite colimits. The functor `equivalence.functor` is definitionally `N`, so the exactness
-- property transfers by `simpa [equivalence]`.
/-- Lemma 14.23.8: the normalized Moore complex functor
`N : SimplicialObject A ⥤ ChainComplex A ℕ` is exact. -/
theorem doldKan_N_exact :
    exactFunctor (SimplicialObject A) (ChainComplex A ℕ)
      (N : SimplicialObject A ⥤ ChainComplex A ℕ) := by
  simpa [equivalence] using
    (ExactFunctor.of
      (equivalence.functor : SimplicialObject A ⥤ ChainComplex A ℕ)).property

end

end CategoryTheory
