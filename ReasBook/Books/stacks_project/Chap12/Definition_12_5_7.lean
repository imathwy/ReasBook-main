import Mathlib.Algebra.Homology.ExactSequence
import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex
import Mathlib.Algebra.Homology.ShortComplex.ShortExact
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.

universe v u

namespace CategoryTheory

/- Domain-style sampling for Definition 12.5.7:
- primary domain: exactness of finite sequences, homological complexes, and short exact sequences
  in categorical homological algebra;
- sampled canonical owner declarations:
  `ComposableArrows.IsComplex`,
  `ComposableArrows.Exact`,
  `ShortComplex.Exact`,
  `ShortComplex.toComposableArrows`,
  `ShortComplex.exact_iff_exact_toComposableArrows`,
  `HomologicalComplex.ExactAt`,
  `HomologicalComplex.Acyclic`,
  `ShortComplex.ShortExact`;
- best owner abstractions:
  `ComposableArrows C n` for finite sequences,
  `ShortComplex C` with the owner predicate `S.Exact` for three-term exact sequences,
  `HomologicalComplex C c` for complexes,
  `ShortComplex C` with the owner predicate `S.ShortExact` for short exact sequences;
- primitive data:
  the underlying finite diagram of composable arrows, the underlying homological complex, and the
  underlying short complex;
- derived API:
  the owner predicates for consecutive-zero compositions, exactness at a spot, acyclicity, and the
  bridge from a three-term short complex to `ComposableArrows C 2`;
- source/core/bridge triage:
  `source-facing`: the textbook notions of finite exact sequences, complexes exact at a term,
    acyclic complexes, exactness of a three-term sequence, and short exact sequences;
  `core/canonical`: `ComposableArrows.Exact`, `ShortComplex.Exact`,
    `HomologicalComplex.ExactAt`, `HomologicalComplex.Acyclic`, and `ShortComplex.ShortExact`;
  `bridge/view`: `ShortComplex.toComposableArrows` and
    `ShortComplex.exact_iff_exact_toComposableArrows`.

No local wrapper should be introduced here: the source notions are already owned by the canonical
mathlib declarations above. For three-term exact sequences, the main owner is `ShortComplex.Exact`,
and the comparison with finite exact sequences is already provided by the owner-side bridge from
`ShortComplex` to `ComposableArrows`.
-/

/- Definition 12.5.7 (finite sequences): for a finite sequence of composable arrows, the owner
predicate for "the composite of any two consecutive arrows is zero" is
`ComposableArrows.IsComplex`, and exactness of the whole finite sequence is
`ComposableArrows.Exact`. -/
recall ComposableArrows.IsComplex
recall ComposableArrows.Exact

/- Definition 12.5.7 (three-term sequences): for a composable pair `X₁ ⟶ X₂ ⟶ X₃` with zero
composite, the canonical owner predicate for exactness is `ShortComplex.Exact`. -/
recall ShortComplex.Exact

/- Companion bridge: for a three-term sequence `X₁ ⟶ X₂ ⟶ X₃`, exactness of the associated short
complex is transported to finite-sequence exactness by `ShortComplex.toComposableArrows`, and
`ShortComplex.exact_iff_exact_toComposableArrows` identifies it with exactness of the
corresponding object of `ComposableArrows C 2`. -/
recall ShortComplex.toComposableArrows
recall ShortComplex.exact_iff_exact_toComposableArrows

/- Definition 12.5.7 (complexes): the owner object for a complex in an additive category is
`HomologicalComplex`, with `ChainComplex` and `CochainComplex` as the standard one-sided
specializations. -/
recall HomologicalComplex
recall ChainComplex
recall CochainComplex

/- Definition 12.5.7 (exactness in a complex): exactness at a chosen object of a homological
complex is defined from the canonical associated short complex `HomologicalComplex.sc`; the owner
predicate `HomologicalComplex.ExactAt` is by definition exactness of that short complex in the
chosen degree. -/
recall HomologicalComplex.sc
recall HomologicalComplex.ExactAt
recall HomologicalComplex.exactAt_iff

/- Definition 12.5.7 (acyclicity): exactness in every degree of a homological complex is the
owner predicate `HomologicalComplex.Acyclic`. -/
recall HomologicalComplex.Acyclic
recall HomologicalComplex.acyclic_iff

/- Definition 12.5.7 (short exact sequences): the owner predicate for a short exact sequence
`0 ⟶ X₁ ⟶ X₂ ⟶ X₃ ⟶ 0` is `S.ShortExact`. -/
recall ShortComplex.ShortExact

/- The constructor `ShortComplex.ShortExact.mk'` gives the textbook formulation directly:
to build short exactness, it suffices to provide exactness together with `Mono S.f`
and `Epi S.g`. -/
recall ShortComplex.ShortExact.mk'

end CategoryTheory
