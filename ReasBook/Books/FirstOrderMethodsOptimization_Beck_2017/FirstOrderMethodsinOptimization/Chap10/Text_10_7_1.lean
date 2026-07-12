import Mathlib
import FirstOrderMethodsOptimization_Beck_2017.Chap01.Definition_1_18
import FirstOrderMethodsOptimization_Beck_2017.Chap10.Theorem_10_34

-- Declarations for this item will be appended below by the statement pipeline.

/- Text 10.7.1 is `bridge/view`: it does not define a second accelerated-method owner, and it
does not define a second weighted-norm owner. Its mathematical role is only to read the general
FISTA `O(1 / k^2)` estimate from Theorem 10.34 in the canonical positive-definite `Q`-geometry on
`ℝ^n`.

Primary domain: fast proximal-gradient rates specialized to a matrix-induced Hilbert geometry on
finite-dimensional real coordinate space.

Domain sampling in the surrounding project API identifies the relevant owner chain:
- `Matrix.toNormedAddCommGroup` from mathlib/Chapter 1 as the owner of the normed additive-group
  structure induced by a positive-definite matrix;
- `Matrix.toInnerProductSpace` from mathlib/Chapter 1 as the owner of the corresponding
  `Q`-inner-product geometry;
- `Matrix.qNorm` from Definition 1.18 as the source-facing Chapter 1 notation/view for that
  induced norm;
- `fista_objective_gap_le_two_alpha_Lf_dist_sq_div_sq` from Theorem 10.34 as the canonical
  Chapter 10 accelerated objective-gap estimate.

Layer triage:
- `source-facing`: the textbook reading of the FISTA rate bound in `Q`-norm notation;
- `core/canonical`: `Matrix.toNormedAddCommGroup`, `Matrix.toInnerProductSpace`, and
  `fista_objective_gap_le_two_alpha_Lf_dist_sq_div_sq`;
- `bridge/view`: `Matrix.qNorm`, which exposes the canonical owner geometry in the source-facing
  notation used for weighted Euclidean space.

Primitive data versus derived API:
- primitive data already live upstream as the positive-definite matrix geometry and the fast
  proximal-gradient problem data used by Theorem 10.34;
- the displayed `Q`-norm notation is derived API from that owner geometry, so no new local
  wrapper theorem or packaged specialization belongs here.

Accordingly this file should stay recall-only, reusing the existing owners directly instead of
keeping a parallel local theorem whose only role would be notational restatement. -/
recall Matrix.toNormedAddCommGroup
recall Matrix.toInnerProductSpace
recall Matrix.qNorm
recall fista_objective_gap_le_two_alpha_Lf_dist_sq_div_sq
