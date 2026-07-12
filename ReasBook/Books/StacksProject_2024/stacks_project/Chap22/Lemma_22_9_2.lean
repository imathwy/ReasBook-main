import Mathlib.Algebra.Homology.HomotopyCategory.DegreewiseSplit
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.

/- Domain-style sampling for Lemma 22.9.2:
- primary domain: admissible short exact sequences of differential graded modules, their
  associated triangles, and the comparison with the mapping-cone triangle of the connecting
  morphism;
- inspected owner declarations:
  `CochainComplex.triangleOfDegreewiseSplit`,
  `CochainComplex.triangleOfDegreewiseSplitRotateRotateIso`,
  `CochainComplex.mappingCone.triangleRotateIsoTriangleOfDegreewiseSplit`;
- best owner abstraction: the source statement is the cochain-level comparison between the doubly
  rotated associated triangle of a degreewise split short exact sequence and the standard
  mapping-cone triangle of its connecting morphism, which is exactly the upstream owner
  `CochainComplex.triangleOfDegreewiseSplitRotateRotateIso`;
- primitive data: an admissible short exact sequence of differential graded modules, viewed on the
  underlying cochain-complex side where the associated triangle and the cone construction are
  defined canonically;
- derived API: the comparison isomorphism itself remains upstream, so this file is a direct recall
  rather than a new wrapper.
-/

/- Source/core/bridge triage:
- `source-facing`: the comparison between the doubly rotated triangle attached to an admissible
  short exact sequence of differential graded modules and the standard mapping-cone triangle of
  the connecting morphism `δ[-1]`;
- `core/canonical`: the cochain-level owner
  `CochainComplex.triangleOfDegreewiseSplitRotateRotateIso`;
- `bridge/view`: no extra bridge is needed here, because the numbered item already lives at the
  cochain-complex level; the homotopy-category bridge appears separately in
  `Lemma_22_27_11`.
-/

/- Lemma 22.9.2: if
`0 ⟶ K ⟶ L ⟶ M ⟶ 0` is an admissible short exact sequence of differential graded modules over a
differential graded algebra and `(K, L, M, α, β, δ)` is its associated triangle, then the
triangles `(M[-1], K, L, δ[-1], α, β)` and `(M[-1], K, C(δ[-1]), δ[-1], i, p)` are isomorphic.
On the underlying cochain-complex side this is exactly the canonical comparison
`CochainComplex.triangleOfDegreewiseSplitRotateRotateIso`. -/
recall CochainComplex.triangleOfDegreewiseSplitRotateRotateIso
