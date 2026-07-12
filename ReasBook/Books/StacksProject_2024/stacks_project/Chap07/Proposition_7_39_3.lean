import Mathlib
import StacksProject_2024.Chap07.Definition_7_38_1
import StacksProject_2024.Chap07.Lemma_7_17_2
import StacksProject_2024.Chap07.Lemma_7_38_3
import StacksProject_2024.Chap07.Lemma_7_39_2
import StacksProject_2024.Chap07.Proposition_7_33_3

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

namespace CategoryTheory

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}

/- Domain-style sampling for Proposition 7.39.3:
- primary domain: enough points on a Grothendieck site, built from point fibers of cofiltered
  inverse systems and the canonical conservative-family criterion;
- sampled owner API:
  `GrothendieckTopology.HasEnoughPoints`,
  `GrothendieckTopology.hasEnoughPoints_iff_exists_conservativePointFamily`,
  `GrothendieckTopology.isConservativePointFamily_iff_exists_point_separating_sections`,
  `GrothendieckTopology.Point.ofIsCofiltered.fiber`,
  `HasFiniteRefinementProperty`;
- source/core/bridge triage:
  `source-facing`: the site-level theorem that the finite-refinement hypothesis implies enough
    points;
  `core/canonical`: `J.HasEnoughPoints` and the owner notion `GrothendieckTopology.Point`;
  `bridge/view`: the separation criterion for conservative families of points and the
    inverse-system fiber construction used to manufacture the required points.

Primitive data are only the finite-limit hypothesis on `C` and the source-facing finite-refinement
assumption `∀ X, J.HasFiniteRefinementProperty X`. Conservative-family packaging and the passage
from a cofiltered inverse system to a point are derived API from the owner layer above, so this
file should stay a thin theorem at the `HasEnoughPoints` owner rather than introducing any local
wrapper around conservative point families or point data.
-/
-- Proof sketch: for any two distinct sections of a sheaf, start with the trivial one-object
-- inverse system at the ambient object and apply Lemma 7.39.2 to obtain a refined inverse system
-- that still separates the sections and whose associated fiber functor is jointly surjective for
-- every finite covering family. The finite-refinement hypothesis upgrades this to all covering
-- families, so Proposition 7.33.3 turns the resulting functor into a point; Lemma 7.38.3 then
-- shows that the resulting family of points is conservative.
/-- Proposition 7.39.3: if finite limits exist in `C` and every covering family in `(C, J)`
admits a finite covering refinement, then `(C, J)` has enough points. -/
theorem hasEnoughPoints_of_finite_cover_refinement
    [Limits.HasFiniteLimits C]
    (hfinite : ∀ X : C, J.HasFiniteRefinementProperty X) :
    J.HasEnoughPoints := sorry

end CategoryTheory
