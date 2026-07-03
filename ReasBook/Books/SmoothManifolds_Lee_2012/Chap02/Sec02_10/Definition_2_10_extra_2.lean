import Mathlib.Geometry.Manifold.BumpFunction
import Mathlib.Tactic.Recall
import SmoothManifoldsLee.Chap02.Sec02_10.Lemma_2_22

/- Definition 2.10-extra-2: The Euclidean cutoff from `Lemma_2.22` is a bundled
`ContDiffBump`, and `SmoothBumpFunction` is the canonical manifold-level generalization used
later in the chapter. -/
recall ContDiffBump

/- The chapter's Euclidean existence theorem is the source-facing bridge to this canonical owner. -/
recall exists_smooth_ball_cutoff

/- `SmoothBumpFunction` is the manifold-level generalization of Euclidean smooth bump functions. -/
recall SmoothBumpFunction
