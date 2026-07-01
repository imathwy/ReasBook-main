import Mathlib.Analysis.InnerProductSpace.Harmonic.Basic
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.

open InnerProductSpace

-- Domain sampling: the harmonic-function owner layer in mathlib is organized around
-- `HarmonicAt`, `HarmonicOnNhd`, and derived API such as `HarmonicOnNhd.contDiffOn`.
-- This textbook definition is therefore a `core/canonical` recall of `HarmonicOnNhd`,
-- not a new source-facing owner.

/- Definition IV.3-extra-1: the textbook notion of a function on an open subset `D` of the plane
being harmonic, meaning that it has continuous second derivatives and vanishing Laplacian on `D`,
is the canonical mathlib notion `InnerProductSpace.HarmonicOnNhd`. This owner is formulated for
functions on finite-dimensional real inner product spaces, so it also covers the textbook
`n`-variable extension. -/
recall HarmonicOnNhd
