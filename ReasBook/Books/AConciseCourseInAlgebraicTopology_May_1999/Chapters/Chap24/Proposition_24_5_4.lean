import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap24.Lemma_24_4_4
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap24.ComplexKTheoryAdams

open scoped ComplexKTheory ComplexKTheoryAdams

noncomputable section

-- The current Chapter 24 API exposes the ambient even rational cohomology owner
-- `EvenRationalCohomology X A`, the Chern-character owner `IsComplexKTheoryChernCharacter ch`,
-- and the Adams-operation owner `IsComplexKTheoryAdams ψ`. What is still missing for
-- Proposition 24.5.4 is a public chapter-level owner for the degree-`2 * r` summand
-- `H^(2 * r)(X; ℚ)` together with the corresponding component morphism
-- `ch_(2 * r) : K(X) → H^(2 * r)(X; ℚ)`.

/-
Proposition 24.5.4

For a compact space `X`, the `2 * r`-degree component `ch_(2 * r)` of the Chern character is an
eigenmap for the Adams operation `ψ^k`, with eigenvalue `k ^ r`.

Blocked in the current repository state: Chapter 24 already provides the ambient owners
`EvenRationalCohomology`, `IsComplexKTheoryChernCharacter`, `ComplexKTheoryAdamsFamily`, and
`IsComplexKTheoryAdams`. However, the approved public API still lacks:

- a canonical owner for the graded summand `H^(2 * r)(X; ℚ)` inside `H^even(X; ℚ)`,
- a public component morphism `ch_(2 * r) : K(X) → H^(2 * r)(X; ℚ)`,
- and the bridge API relating that component to the ambient even rational cohomology owner.

A source-faithful theorem statement should therefore be added only after that graded Chapter 24
owner exists, rather than by packaging the component as ad hoc local projection data in this file.
-/
#check EvenRationalCohomology
#check IsComplexKTheoryChernCharacter
#check ComplexKTheoryAdamsFamily
#check IsComplexKTheoryAdams
