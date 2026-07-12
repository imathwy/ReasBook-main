import StacksProject_2024.Chap18.Definition_18_32_6
import StacksProject_2024.Chap31.Definition_31_26_7

-- Declarations for this item will be appended below by the statement pipeline.

open AlgebraicGeometry

-- Semantic recall / owner check:
-- Local Chapter 31 inspection found the endpoint owners already present, while the actual
-- divisor-of-meromorphic-section owner and comparison map `Pic(X) → Cl(X)` are still absent as
-- local declarations.

/- Lemma 31.27.5: let `X` be a locally Noetherian integral scheme. The source says that nonzero
meromorphic sections of invertible modules
multiply, their divisors add in `Div(X)`, and consequently the induced class in `Cl(X)` is
additive under tensor product. The current project still lacks a scheme-level owner for
`div_\mathcal{L}(s)` and for the comparison map `\mathrm{Pic}(X) \to \mathrm{Cl}(X)`. The
supporting principal-divisor, meromorphic-section, and denominator-ideal APIs already live in
earlier Chapter 31 files, while the endpoint owners are already available as the canonical
ringed-site Picard group of the underlying ringed space and `Cl(X)`. This file therefore remains a
labeled recall-only block for those comparison-map endpoints. -/
#check ringedSitePicardGroup
#check WeilDivisorClassGroup
