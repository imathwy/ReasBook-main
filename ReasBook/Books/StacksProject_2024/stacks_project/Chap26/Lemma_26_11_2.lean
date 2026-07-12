import Mathlib.AlgebraicGeometry.AffineScheme
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.

open AlgebraicGeometry

/- Source/core/bridge triage for Lemma 26.11.2:
- `source-facing`: the affine open subsets of a scheme form a basis for its topology;
- `core/canonical`: the exact owner `Scheme.isBasis_affineOpens`;
- `bridge/view`: this item is recall-only, so the faithful refine is to reuse the canonical basis
  owner directly on the subtype `X.affineOpens` rather than restating it through a local alias,
  wrapper theorem, or expanded set expression. -/

-- Semantic recall: mathlib already provides the exact canonical owner
-- `AlgebraicGeometry.Scheme.isBasis_affineOpens`, so this Stacks item is a pure recall of the
-- existing scheme-topology API rather than a place for a parallel local theorem.

/- Lemma 26.11.2: the collection of affine opens of a scheme forms a basis for the topology on
the scheme. In mathlib this is exactly `AlgebraicGeometry.Scheme.isBasis_affineOpens`, so this
item is recorded as a pure canonical recall of the existing owner. -/
recall Scheme.isBasis_affineOpens

section

universe u

variable (X : Scheme.{u})

#check
  (Scheme.isBasis_affineOpens X :
    TopologicalSpace.Opens.IsBasis X.affineOpens)

end
