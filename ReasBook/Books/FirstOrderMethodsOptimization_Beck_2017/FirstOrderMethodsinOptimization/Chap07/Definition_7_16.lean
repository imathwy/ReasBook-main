import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

/- Definition 7.16: the textbook diagonal-matrix construction `dg(v)` is the canonical mathlib
owner `Matrix.diagonal`, which sends a vector `v` to the square matrix whose diagonal entries are
given by `v` and whose off-diagonal entries are zero. -/
recall Matrix.diagonal

/- The textbook entrywise formula for `dg(v)` is the canonical pointwise statement
`Matrix.diagonal_apply`. -/
recall Matrix.diagonal_apply
