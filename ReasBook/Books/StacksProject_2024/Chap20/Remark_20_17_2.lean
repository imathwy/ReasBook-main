import Mathlib.Tactic.Recall
import stacks_project.Chap20.Remark_20_28_3

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open ComplexShape
open AlgebraicGeometry
open TopologicalSpace

noncomputable section

universe u

namespace AlgebraicGeometry.RingedSpace

attribute [local instance] HasDerivedCategory.standard

/- Domain-style sampling for Remark 20.17.2:
- primary domain: unbounded derived pullback/pushforward for sheaves of modules on ringed spaces,
  and the associated base-change morphism for a commutative square;
- sampled owner declarations:
  `RingedSpace.Modules`,
  `RingedSpace.Hom.pushforward`,
  `modulePullbackDerived`,
  `exists_unbounded_derived_baseChange_map`;
- best owner abstraction: the chapter owner theorem
  `AlgebraicGeometry.RingedSpace.exists_unbounded_derived_baseChange_map` from
  `Remark_20_28_3`;
- primitive data: a square of ringed-space morphisms, the chosen derived adjunctions
  `Lf^* ⊣ Rf_*` and `L(f')^* ⊣ R(f')_*`, and the pullback-commutativity isomorphism
  `L(f')^* ⋙ Lg^* ≅ L(g')^* ⋙ Lf^*`;
- derived API: the source and target objects
  `Lg^* Rf_* K` and `R(f')_* L(g')^* K`, together with the adjoint-transpose characterization of
  the base-change morphism.

Source/core/bridge triage:
- `source-facing`: the existence of the unbounded derived base-change morphism for a square of
  ringed spaces;
- `core/canonical`: the owner theorem
  `AlgebraicGeometry.RingedSpace.exists_unbounded_derived_baseChange_map`;
- `bridge/view`: this numbered remark is recall-only. It should reuse that owner directly rather
  than restating the same sheaf/module/derived-category setup and theorem under a parallel local
  API.
-/

/- Remark 20.17.2: the correct base-change morphism is the unbounded derived map
`Lg^* Rf_* \mathcal F^\bullet ⟶ R(f')_* L(g')^* \mathcal F^\bullet`. In the current chapter
development this is already the owner theorem
`AlgebraicGeometry.RingedSpace.exists_unbounded_derived_baseChange_map`, so this file should be a
direct recall rather than a second duplicate declaration block. -/
recall exists_unbounded_derived_baseChange_map

end AlgebraicGeometry.RingedSpace
