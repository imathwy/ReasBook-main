import Mathlib.Tactic.Recall
import StacksProject_2024.stacks_project.Chap20.Open_subspace_module_owners

-- Declarations for this item will be appended below by the statement pipeline.

namespace AlgebraicGeometry.RingedSpace

/- Domain-style sampling for Lemma 20.32.1:
- primary domain: restriction of derived `𝒪_X`-modules to an open subspace and
  preservation of K-injectivity under the canonical extension-by-zero adjunction;
- sampled canonical/project declarations:
  `moduleRestrictionToOpen`,
  `modulePushforwardFromOpen`,
  `moduleRestrictionToOpen_isKInjective`;
- best owner abstraction:
  `source-facing`: Lemma `20.32.1`, the K-injective preservation statement for restriction to an
    open subspace;
  `core/canonical`: the Chapter 20 owner theorem `moduleRestrictionToOpen_isKInjective` on the
    open-subspace module owner layer;
  `bridge/view`: this numbered file is the direct recall surface for that owner theorem.
- primitive data: the ringed space `X`, the open subset `U`, and the K-injective complex `I`;
- derived API: the recalled owner theorem itself.

This file therefore keeps the numbered item as a recall surface and does not duplicate the owner
proof or a parallel theorem wrapper.
-/

/- Lemma 20.32.1: restriction of a K-injective complex of `𝒪_X`-modules to an open
subspace remains K-injective. This is exactly the owner theorem
`moduleRestrictionToOpen_isKInjective`. -/
recall moduleRestrictionToOpen_isKInjective

end AlgebraicGeometry.RingedSpace
