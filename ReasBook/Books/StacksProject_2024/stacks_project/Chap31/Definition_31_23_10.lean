import Mathlib
import Mathlib.Tactic.Recall
import StacksProject_2024.Chap31.Lemma_31_23_9

-- Declarations for this item will be appended below by the statement pipeline.

-- Semantic recall / owner check:
-- `lean_leansearch` surfaced generic ideal-sheaf owners such as `Scheme.IdealSheafData`, while
-- local Chapter 31 inspection showed that Lemma 31.23.9 already packages the source-defined
-- denominator data in `Scheme.RegularMeromorphicSectionIdealSheaf`, with the ideal sheaf itself
-- exposed by the companion abbreviation `RegularMeromorphicSectionIdealSheaf.idealSheaf`. This
-- item therefore stays a labeled recall-only block rather than introducing a duplicate alias for
-- that owner.

/- Definition 31.23.10: let `X` be a scheme, let `\mathcal L` be an invertible
`\mathcal O_X`-module, and let `s` be a regular meromorphic section of `\mathcal L`. The sheaf of
ideals `\mathcal I` constructed in Lemma 31.23.9 is called the ideal sheaf of denominators of
`s`. In the current project, this source-facing owner is the existing companion abbreviation
`AlgebraicGeometry.Scheme.RegularMeromorphicSectionIdealSheaf.idealSheaf`. -/
recall AlgebraicGeometry.Scheme.RegularMeromorphicSectionIdealSheaf.idealSheaf
