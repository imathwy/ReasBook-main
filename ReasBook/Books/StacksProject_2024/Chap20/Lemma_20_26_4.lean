import Mathlib
import stacks_project.Chap17.Definition_17_4_1
import stacks_project.Chap18.Lemma_18_36_3
import stacks_project.Chap20.Definition_20_26_2

-- Declarations for this item will be appended below by the statement pipeline.

open AlgebraicGeometry
open CategoryTheory
open ComplexShape

noncomputable section

namespace AlgebraicGeometry.RingedSpace

variable {X : RingedSpace}
variable [MonoidalCategory (RingedSpace.Modules X)] [MonoidalPreadditive (RingedSpace.Modules X)]

/- Domain-style sampling:
- primary domain: stalk functors on sheaves of modules over a ringed space and K-flatness of
  cochain complexes;
- sampled owner declarations:
  `CategoryTheory.point_sheaf_module_stalk_functor`,
  `CategoryTheory.point_stalk_ring`,
  `CategoryTheory.Functor.mapHomologicalComplex`,
  `CochainComplex.IsKFlat`;
- best owner abstraction: the site-point stalk functor
  `point_sheaf_module_stalk_functor (Opens.pointGrothendieckTopology x) (RingedSpace.ringCatSheaf X)`; the
  stalk complex is then the canonical derived API obtained via `mapHomologicalComplex`;
- primitive data: a point `x : X` and a complex `K : CochainComplex (RingedSpace.Modules X) ℤ`;
- derived API: the induced stalk complex and its K-flatness predicate.

Source/core/bridge triage:
- `source-facing`: Lemma 20.26.4, which detects K-flatness of a complex on stalks;
- `core/canonical`: `point_sheaf_module_stalk_functor`, `Functor.mapHomologicalComplex`, and
  `CochainComplex.IsKFlat`;
- `bridge/view`: the specialization from the canonical site point `Opens.pointGrothendieckTopology x`
  to the ringed-space stalk functor; no separate local owner is introduced here. -/

-- Proof sketch: for the forward implication, apply K-flatness to the skyscraper-module complex
-- attached to an acyclic stalk complex and then evaluate at `x`. For the converse, test acyclicity
-- of `Tot(F ⊗ K)` on stalks; stalks commute with tensor products and exactness is stalkwise.
/-- Lemma 20.26.4: a complex `\mathcal K^\bullet` of `\mathcal O_X`-modules is K-flat if and only
if, for every point `x : X`, the stalk complex obtained by applying the canonical stalk functor
`point_sheaf_module_stalk_functor (Opens.pointGrothendieckTopology x) (RingedSpace.ringCatSheaf X)` is
K-flat. -/
theorem isKFlat_iff_stalkwise_isKFlat (K : CochainComplex (RingedSpace.Modules X) ℤ) :
    IsKFlat K ↔
      ∀ x : X, IsKFlat
        (((point_sheaf_module_stalk_functor (Opens.pointGrothendieckTopology x)
            (RingedSpace.ringCatSheaf X)).mapHomologicalComplex (up ℤ)).obj K) := sorry

end AlgebraicGeometry.RingedSpace
