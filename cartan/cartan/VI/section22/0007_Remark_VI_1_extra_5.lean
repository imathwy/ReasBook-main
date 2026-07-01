import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

-- Semantic recall note: the requested `lean_leansearch` tool was unavailable in this runner, so
-- the owner-level API was checked directly against
-- `Mathlib/Topology/Compactification/OnePoint/Basic.lean`, in particular `OnePoint`,
-- `OnePoint.isOpenEmbedding_coe`, and `OnePoint.isOpen_image_coe`.

/-
Remark VI.1-extra-5 is a `core/canonical` recall item in the topology of the Riemann sphere. The
owner object is `OnePoint`; the complex plane sits inside `OnePoint ℂ` by the canonical coercion
`ℂ → OnePoint ℂ`, this inclusion is an open embedding, and openness on the finite chart is exactly
transported by `OnePoint.isOpen_image_coe`. No local Riemann-sphere wrapper is needed here.
-/
recall OnePoint
recall OnePoint.some
recall OnePoint.isOpenEmbedding_coe
recall OnePoint.isOpen_image_coe
