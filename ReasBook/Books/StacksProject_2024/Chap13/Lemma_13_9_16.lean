import Mathlib.Algebra.Homology.HomotopyCategory.DegreewiseSplit
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.

/- Source/core/bridge triage for Lemma 13.9.16:
- primary domain: triangles in the homotopy category of cochain complexes arising from degreewise
  split short exact sequences, and their comparison with the standard mapping-cone triangle of the
  connecting morphism;
- inspected owner declarations:
  `CochainComplex.triangleOfDegreewiseSplitRotateRotateIso`,
  `CochainComplex.trianglehOfDegreewiseSplitRotateRotateIso`,
  `CochainComplex.trianglehOfDegreewiseSplit`,
  `CochainComplex.mappingCone.triangleh`;
- best owner abstraction: for the chapter statement, the main public entry is the existing
  homotopy-category bridge
  `CochainComplex.trianglehOfDegreewiseSplitRotateRotateIso`; the cochain-level comparison
  `CochainComplex.triangleOfDegreewiseSplitRotateRotateIso` remains the upstream core owner and is
  not duplicated locally;
- source/core/bridge triage:
  `source-facing`: the comparison in `K(𝒜)` between the doubly rotated triangle attached to a
    degreewise split short complex and the mapping-cone triangle of its connecting morphism;
  `core/canonical`: the cochain-level owner
    `CochainComplex.triangleOfDegreewiseSplitRotateRotateIso`;
  `bridge/view`: the induced homotopy-category isomorphism
    `CochainComplex.trianglehOfDegreewiseSplitRotateRotateIso`;
- primitive data: a short complex `S : ShortComplex (CochainComplex 𝒜 ℤ)` and a degreewise
  splitting family `σ`;
- derived API: the connecting morphism `CochainComplex.homOfDegreewiseSplit S σ`, the homotopy
  triangle `CochainComplex.trianglehOfDegreewiseSplit S σ`, and the canonical bridge to the
  standard mapping-cone triangle all remain upstream and are reused directly here.
-/

/- Lemma 13.9.16: for a degreewise split short exact sequence of cochain complexes in an additive
category with binary biproducts, the doubly rotated triangle in `K(𝒜)` attached to that split
sequence is canonically isomorphic to the standard mapping-cone triangle of the connecting
morphism. This is exactly the upstream bridge
`CochainComplex.trianglehOfDegreewiseSplitRotateRotateIso`. -/
recall CochainComplex.trianglehOfDegreewiseSplitRotateRotateIso
