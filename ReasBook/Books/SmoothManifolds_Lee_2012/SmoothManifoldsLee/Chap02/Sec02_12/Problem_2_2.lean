import Mathlib.Tactic.Recall
import SmoothManifolds_Lee_2012.SmoothManifoldsLee.Chap02.Sec02_08.Proposition_2_12

-- Declarations for this item will be appended below by the statement pipeline.

open scoped Manifold ContDiff

-- Domain sampling pass: this item is in the finite-product smooth-manifold `ContMDiff` API.
-- Sampled owner declarations:
-- * mathlib: `ModelWithCorners.pi`
-- * mathlib: `contMDiffAt_pi_space`
-- * mathlib: `contMDiff_pi_space`
-- * project: `contMDiff_pi_iff`
-- The core owner abstraction is the canonical product-manifold smoothness statement
-- `ContMDiff J (ModelWithCorners.pi I) n Φ`. The component maps are derived bridge/view API, so
-- this `Ch2` file recalls the importable chapter owner theorem rather than keeping a second local
-- theorem with the same mathematical content.

/- Problem 2-2: a map into a finite product manifold is smooth if and only if each component map
is smooth. -/
recall contMDiff_pi_iff
