import Mathlib.Tactic.Recall
import ConvexAnalysis_Rockafellar_1970.Chap01.Definition_4_1

-- Declarations for this item will be appended below by the statement pipeline.

/-!
Source/core/bridge triage:

- `source-facing`: Definition 6.27.9 names the epigraph of an ordered-extended-codomain function
  `h : E → WithTopBot α` as the set of pairs `(x, μ)` with `h x ≤ μ`.
- `core/canonical`: the project already owns this notion in Chapter 1 as `epi`, together with
  the textbook notations `epi[S] f` and `epi f`.
- `bridge/view`: owner-level membership (`mem_epi_iff`) is the intrinsic API surface, and the
  global source set-builder formula is the companion bridge `epi_univ_eq_setOf_le`.
- Primitive data vs derived API: the only primitive datum is the function `h`; the global set
  description and membership rewrites are derived from the Chapter 1 owner.
- Layer target: `core/canonical recall/use`.

Domain-style sampling used here:
- `epi`;
- `mem_epi_iff`;
- `epi_univ_eq_setOf_le`;
- `epi_restrict_eq_preimage_fst_inter`.
-/

/- Definition 6.27.9: Rockafellar's epigraph is the existing chapter owner `epi`,
specialized to the full domain and written downstream as `epi h`. -/
recall epi

/- Intrinsic owner-level membership for the global epigraph surface. -/
recall mem_epi_iff

/- The source's global set formula is already the chapter owner theorem
`epi_univ_eq_setOf_le`, so this file reuses it directly instead of keeping a renamed shell. -/
recall epi_univ_eq_setOf_le
