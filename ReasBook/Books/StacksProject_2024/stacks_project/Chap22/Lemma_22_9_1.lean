import Mathlib.Algebra.Homology.HomotopyCategory.DegreewiseSplit
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.

/- Domain-style sampling for Lemma 22.9.1:
- primary domain: mapping-cone triangles and triangles attached to degreewise split short exact
  sequences of differential graded modules;
- inspected owner declarations:
  `CochainComplex.mappingCone.triangle`,
  `CochainComplex.triangleOfDegreewiseSplit`,
  `CochainComplex.triangleRotateShortComplex`,
  `CochainComplex.mappingCone.triangleRotateIsoTriangleOfDegreewiseSplit`;
- best owner abstraction: the upstream mapping-cone owner comparison
  `CochainComplex.mappingCone.triangleRotateIsoTriangleOfDegreewiseSplit`;
- primitive data: a morphism of differential graded modules, formalized on the underlying
  cochain-complex side where cones, shifts, and associated triangles live canonically in mathlib;
- derived API: the rotated standard mapping-cone triangle, the canonical degreewise split short
  complex `0 ⟶ L ⟶ C(f) ⟶ K[1] ⟶ 0`, and the resulting triangle comparison remain upstream and
  are reused directly here.
-/

/- Source/core/bridge triage:
- `source-facing`: the textbook identification of the triangle `(L, C(f), K[1], i, p, f[1])`
  attached to the cone short exact sequence of a morphism of differential graded modules;
- `core/canonical`: the cochain-level owner comparison
  `CochainComplex.mappingCone.triangleRotateIsoTriangleOfDegreewiseSplit`;
- `bridge/view`: no extra bridge is needed in this file, because the numbered item is a direct
  recall of the canonical owner rather than a new wrapper isomorphism.
-/

/- Lemma 22.9.1: for a homomorphism `f : K ⟶ L` of differential graded `A`-modules, the
admissible short exact sequence `0 ⟶ L ⟶ C(f) ⟶ K[1] ⟶ 0` coming from the cone definition has
associated triangle `(L, C(f), K[1], i, p, f[1])`. On the canonical mathlib owner side, this is
exactly `CochainComplex.mappingCone.triangleRotateIsoTriangleOfDegreewiseSplit`. -/
recall CochainComplex.mappingCone.triangleRotateIsoTriangleOfDegreewiseSplit
