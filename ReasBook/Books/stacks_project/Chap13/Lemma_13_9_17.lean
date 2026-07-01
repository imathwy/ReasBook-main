import Mathlib.Algebra.Homology.HomotopyCategory.DegreewiseSplit
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.

/- Domain-style sampling for Lemma 13.9.17:
- primary domain: mapping-cone triangles and triangles attached to degreewise split short
  complexes of cochain complexes;
- inspected owner declarations:
  `CochainComplex.mappingCone.triangle`,
  `CochainComplex.triangleOfDegreewiseSplit`,
  `CochainComplex.triangleOfDegreewiseSplitRotateRotateIso`,
  `CochainComplex.mappingCone.triangleRotateIsoTriangleOfDegreewiseSplit`;
- best owner abstraction: the upstream mapping-cone owner comparison
  `CochainComplex.mappingCone.triangleRotateIsoTriangleOfDegreewiseSplit`;
- primitive data: a morphism of cochain complexes `f : K^• ⟶ L^•`;
- derived API: the rotated standard mapping-cone triangle, the canonical degreewise split short
  complex `triangleRotateShortComplex f`, its degreewise splitting, and the resulting triangle
  comparison all remain upstream and are reused directly here.
-/

/- Source/core/bridge triage:
- `source-facing`: the textbook identification of the triangle
  `(L^•, C(f)^•, K^•[1], i, p, f[1])`;
- `core/canonical`: the cochain-level owner comparison
  `CochainComplex.mappingCone.triangleRotateIsoTriangleOfDegreewiseSplit`;
- `bridge/view`: no extra bridge is needed in this file, because the numbered lemma is already a
  direct recall of the core owner rather than a new wrapper.
-/

/- Lemma 13.9.17: for a morphism of cochain complexes `f : K^• ⟶ L^•` in an additive category,
the termwise split short complex
`0 ⟶ L^• ⟶ C(f)^• ⟶ K^•[1] ⟶ 0` coming from the definition of the cone has associated triangle
the rotated mapping-cone triangle; this is the mathlib formalization of the book's triangle
`(L^•, C(f)^•, K^•[1], i, p, f[1])`. The canonical identification is
`CochainComplex.mappingCone.triangleRotateIsoTriangleOfDegreewiseSplit`. -/
recall CochainComplex.mappingCone.triangleRotateIsoTriangleOfDegreewiseSplit
