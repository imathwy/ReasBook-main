import Mathlib.Algebra.Homology.HomotopyCategory.DegreewiseSplit
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.

/- Domain-style sampling for Lemma 22.27.11:
- primary domain: the triangle in `K(𝒜)` attached to an admissible short exact sequence of
  cochain complexes, and its comparison with the standard mapping-cone triangle of the connecting
  morphism;
- inspected owner declarations:
  `CochainComplex.trianglehOfDegreewiseSplitRotateRotateIso`,
  `CochainComplex.triangleOfDegreewiseSplitRotateRotateIso`,
  `CochainComplex.mappingCone.trianglehRotateIsoTrianglehOfDegreewiseSplit`;
- best owner abstraction: the source statement already lives in the homotopy category, so the
  main public entry should be the homotopy-category comparison
  `CochainComplex.trianglehOfDegreewiseSplitRotateRotateIso`, with the cochain-level comparison
  kept only as a companion recall. -/

/- Source/core/bridge triage for Lemma 22.27.11:
- `source-facing`: the comparison in `K(𝒜)` between the rotated triangle attached to an
  admissible short exact sequence in `Comp(𝒜)` from Situation `22.27.2` and the standard
  mapping-cone triangle of the connecting morphism `δ[-1]`;
- `core/canonical`: the cochain-level bridge
  `CochainComplex.triangleOfDegreewiseSplitRotateRotateIso`;
- `bridge/view`: the induced homotopy-category isomorphism
  `CochainComplex.trianglehOfDegreewiseSplitRotateRotateIso`;
- local precedent: the same owner choice is used in [Lemma_13_9_16](/volume/math/users/zcwang/m2f-distributed-workspace/repos/stacks-refine-stmt/stacks_project/Chap13/Lemma_13_9_16.lean:1).
-/

/- Lemma 22.27.11: in Situation `22.27.2`, if `x ⟶ y ⟶ z` is an admissible short exact sequence
in `Comp(𝒜)` with associated triangle `(x, y, z, α, β, δ)` in `K(𝒜)`, then the triangles
`(z[-1], x, y, δ[-1], α, β)` and `(z[-1], x, c(δ[-1]), δ[-1], i, p)` are canonically isomorphic.
After passing to the underlying degreewise split short complex, this is exactly the upstream
homotopy-category comparison
`CochainComplex.trianglehOfDegreewiseSplitRotateRotateIso`. -/
recall CochainComplex.trianglehOfDegreewiseSplitRotateRotateIso

/- Companion recall: before passing to `K(𝒜)`, the underlying cochain-level comparison is the
canonical isomorphism `CochainComplex.triangleOfDegreewiseSplitRotateRotateIso`. -/
recall CochainComplex.triangleOfDegreewiseSplitRotateRotateIso
