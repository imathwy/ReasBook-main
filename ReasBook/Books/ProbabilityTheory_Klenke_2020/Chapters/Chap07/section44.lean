import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Corollary_7_44 (from Items/Chap07) -/
/- Corollary 7.44: Jordan's decomposition theorem is the canonical equivalence between signed
measures and Jordan decompositions. For a signed measure `φ`, the corresponding Jordan
decomposition has finite mutually singular positive and negative parts
`φ.toJordanDecomposition.posPart` and `φ.toJordanDecomposition.negPart`, and the inverse map
`JordanDecomposition.toSignedMeasure` encodes uniqueness of this decomposition. -/
recall MeasureTheory.SignedMeasure.toJordanDecompositionEquiv
