import Mathlib.RepresentationTheory.Irreducible
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.

-- Source/core/bridge triage:
-- * source-facing: Serre's exercise says that an irreducible finite-dimensional complex
--   representation of an abelian group has degree `1`.
-- * core/canonical: this is exactly the mathlib owner theorem
--   `Representation.IsIrreducible.finrank_eq_one_of_isMulCommutative`.
-- * bridge/view: none is needed here, since the source statement is a direct specialization of the
--   canonical owner theorem rather than an additional construction.
--
-- Primitive data are only a representation `ρ`, its irreducibility, finite-dimensionality over an
-- algebraically closed field, and the commutativity hypothesis on the group. The degree-one
-- conclusion is derived directly from the owner theorem, so a pure `recall` item is the canonical
-- surface.
/- Exercise 3-3.1-3: a finite-dimensional irreducible complex representation of an abelian group
has degree `1`; this is the existing theorem
`Representation.IsIrreducible.finrank_eq_one_of_isMulCommutative`, which does not assume the group
is finite. -/
recall Representation.IsIrreducible.finrank_eq_one_of_isMulCommutative
