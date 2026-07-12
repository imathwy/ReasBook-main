import Mathlib
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory.Limits

universe w v u

namespace CategoryTheory

variable (A : Type u) [Category.{v} A] [Abelian A] [IsGrothendieckAbelian.{w} A]

/- Domain-style sampling for Lemma 19.13.2:
- primary domain: existence of products and limits in Grothendieck abelian categories;
- sampled owner declarations:
  `HasProducts`,
  `hasProductsOfShape_of_hasProducts`,
  `AB4Star`,
  `IsGrothendieckAbelian.hasLimits`;
- best owner abstraction: the source-facing owner for the lemma is `HasProducts A`, while the
  stronger core justification is the instance `IsGrothendieckAbelian.hasLimits`;
- primitive data: an abelian category equipped with `IsGrothendieckAbelian`;
- derived API: `HasProductsOfShape J A` for each indexing type `J`, and more generally all small
  limits in `A`.

Source/core/bridge triage:
- `source-facing`: the Stacks lemma that a Grothendieck abelian category has `AB3*`, i.e.
  the canonical product structure `HasProducts A`;
- `core/canonical`: the stronger owner instance `IsGrothendieckAbelian.hasLimits`;
- `bridge/view`: the standard specialization `hasProductsOfShape_of_hasProducts` from global
  products to products of a fixed shape.

This item adds no new theorem: the faithful refinement is to recall the canonical source-facing
owner `HasProducts` and use `IsGrothendieckAbelian.hasLimits` only as justification, rather than
shifting the public statement to the stronger all-limits instance. -/

/- Lemma 19.13.2: a Grothendieck abelian category has `AB3*`, i.e. it has products; this is
the canonical structure `HasProducts A`, justified upstream by the stronger instance
`IsGrothendieckAbelian.hasLimits`. -/
recall HasProducts

end CategoryTheory
