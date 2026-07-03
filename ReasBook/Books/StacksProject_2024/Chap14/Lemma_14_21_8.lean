import StacksProject_2024.Chap14.Lemma_14_21_7

-- Declarations for this item will be appended below by the statement pipeline.

open scoped Simplicial

universe u

namespace SSet

/- Domain-style sampling for Lemma 14.21.8:
- primary domain: finite simplicial sets and filtrations of subcomplex inclusions by successive
  single-simplex extensions;
- sampled owner-style declarations:
  `SSet.Finite`,
  `SSet.Subcomplex.N`,
  `SSet.Subcomplex.ofSimplex`,
  `RelSeries`;
- best owner abstraction:
  `source-facing`: the existence of a finite chain `U = W₀ ⊆ ⋯ ⊆ W_r = V` whose successive
  inclusions are single-simplex extensions with the boundary of the attached simplex already in
  the previous stage;
  `core/canonical`: finiteness through `SSet.Finite`, single-step extension data through
  `Subcomplex.N`, `Subcomplex.N.boundary_range_le`, and `Subcomplex.ofSimplex`, and finite chains
  through `RelSeries`;
  `bridge/view`: the anonymous adjacent-step relation on `V.Subcomplex`, used only inside the
  filtration existence theorem because it has no separate owner-level downstream role;
- primitive data:
  only the new simplex `x : U.N`, the boundary-factorization predicate `x.boundary_range_le`, and
  the equality `U ⊔ Subcomplex.ofSimplex x.simplex = W` for each step of the chain;
- derived API:
  the ambient finiteness owner `SSet.Finite` and the source-facing finite chain expressed by
  `RelSeries`.

The finite-chain owner is `RelSeries`, so the public source-facing existence statement should use
that canonical owner directly. The adjacent-step predicate is only a bridge/view used inside this
one theorem, so it should not survive as a second public owner declaration. In particular,
`SSet.Finite V` already supplies the degreewise finiteness consequences needed for the textbook
hypothesis, so the filtration theorem should consume that owner canonically as an instance rather
than as a separate named public hypothesis. -/

-- Proof sketch: convert the finiteness hypotheses on nondegenerate simplices into a finite number
-- of missing nondegenerate simplices of `V` outside `U`, and induct on that number. At each step,
-- pick one of minimal degree, adjoin all of its degeneracies to obtain the next subcomplex, verify
-- that every proper face of the chosen simplex already lies in the previous stage by minimality,
-- and iterate until reaching `V`.
/-- Lemma 14.21.8: if `U ⊆ V` is an inclusion of simplicial sets, if `V` is degreewise finite,
and if `V` has finitely many nondegenerate simplices, then there
exists a finite filtration from `U` to `V` whose successive inclusions are single-simplex
extensions in the sense of Lemma 14.21.7. Here the finite chain is expressed by the canonical
owner `RelSeries`, starting at `U` and ending at `⊤ : V.Subcomplex`; the adjacent-step predicate
is kept inline because it is only a bridge/view for this one source-facing theorem. The degreewise
finiteness of `V` is already part of the canonical owner `SSet.Finite V`, and the corresponding
finiteness data for `U` is derived by the subcomplex instance. -/
theorem exists_singleSimplexExtensionFiltration
    {V : SSet.{u}} [V.Finite] (U : V.Subcomplex) :
    ∃ s : RelSeries
      ({ p | ∃ x : p.1.N,
        x.boundary_range_le ∧ p.1 ⊔ Subcomplex.ofSimplex x.simplex = p.2 } :
        SetRel V.Subcomplex V.Subcomplex),
      s.head = U ∧ s.last = (⊤ : V.Subcomplex) := sorry

end SSet
