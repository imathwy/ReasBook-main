import Mathlib
import StacksProject_2024.Chap07.Definition_7_43_2
import StacksProject_2024.Chap07.Definition_7_43_6

-- Declarations for this item will be appended below by the statement pipeline.

universe u v w

namespace CategoryTheory

section

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)

/- Domain-style sampling for Lemma 7.43.5:
- primary domain: closed subtopoi of a sheaf topos, presented by subterminal sheaves;
- sampled owner API:
  `IsClosedSubtopos`,
  `IsSubtopos`,
  `MorphismOfTopoiIn.isSubtopos_essImage`,
  `Over.forget`;
- best owner abstraction: the source-facing predicate `IsClosedSubtopos` on object properties of
  `Sheaf J (Type w)`;
- primitive data: a subterminal sheaf cutting out the object property, exactly as stored by
  `IsClosedSubtopos`;
- derived API: the induced `IsSubtopos` structure.

Source/core/bridge triage:
- `source-facing`: `IsClosedSubtopos`;
- `core/canonical`: `IsSubtopos`;
- `bridge/view`: this lemma upgrades the source-facing closed-subtopos predicate to the canonical
  subtopos predicate, so the owner-level statement should be primary rather than a repeated
  pointwise specialization. -/
-- Proof sketch: unpack the subterminal sheaf witnessing `hP`, then present the resulting full
-- subcategory by the embedding of topoi attached to the site whose coverings are enlarged by the
-- pullback of that subterminal sheaf, as in the Stacks Project proof.
/-- Lemma 7.43.5: every closed subtopos of `Sh(𝒞)` is a subtopos. -/
theorem IsClosedSubtopos.isSubtopos
    {P : ObjectProperty (Sheaf J (Type w))} (hP : IsClosedSubtopos P) :
    IsSubtopos J P := by
  sorry

end

end CategoryTheory
