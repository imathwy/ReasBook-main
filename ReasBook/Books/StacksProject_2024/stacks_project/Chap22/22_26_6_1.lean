import Mathlib.Algebra.Homology.HomotopyCategory.HomComplexCohomology
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.

open CochainComplex.HomComplex

-- Semantic recall check: the source-facing content here is the homogeneous-component sign formula
-- for the differential in the canonical Hom complex. The core owner is `δ_v`, and the degree-`0`
-- specialization used immediately below is the companion owner `δ_zero_cochain_v`. As in the
-- Chapter 15 analogue, this file is a direct recall block rather than a duplicate local wrapper.

/- 22.26.6.1: for a homogeneous component `f_{p, q}` in the Hom complex, the differential is
`d_B ≫ f_{p, q} - (-1)^(p + q) f_{p, q} ≫ d_A`; in mathlib this is the canonical component formula
`δ_v` for the differential on `CochainComplex.HomComplex`, with
`p + q` interpreted as the total cochain degree of `f_{p, q}`. -/
recall δ_v

/- Companion recall: in total degree `0`, the same Hom-complex differential formula specializes to
the standard Leibniz rule for degree-`0` cochains. -/
recall δ_zero_cochain_v
