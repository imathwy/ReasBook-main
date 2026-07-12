import Mathlib.Algebra.Homology.HomotopyCategory.HomComplexCohomology
import Mathlib.Algebra.Homology.HomologySequence
import Mathlib.Algebra.Homology.HomologySequenceLemmas
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.

open ComplexShape
open CochainComplex.HomComplex.CohomologyClass
open HomologicalComplex.HomologySequence

universe v u

namespace CategoryTheory

-- Semantic search note: `lean_leansearch` was unavailable in this runner; owner/API choices were
-- checked against local Chapter 24/21 Hom-complex recall files and the corresponding mathlib
-- homotopy-category homology-sequence API.

/- Domain-style sampling for Remark 24.25.3:
- primary domain: Hom-complex cohomology, morphisms in the homotopy category into shifts, and the
  long exact cohomology sequence attached to a short exact sequence of cochain complexes.
- inspected canonical declarations:
  `CochainComplex.HomComplex.homologyAddEquiv`,
  `homAddEquiv`,
  `ShortComplex.ShortExact.δ`,
  `ShortComplex.ShortExact.homology_exact₁`,
  `ShortComplex.ShortExact.homology_exact₂`,
  `ShortComplex.ShortExact.homology_exact₃`,
  `HomologicalComplex.HomologySequence.composableArrows₅`,
  `HomologicalComplex.HomologySequence.composableArrows₅`,
  `HomologicalComplex.HomologySequence.composableArrows₅_exact`.
- owner abstraction: the canonical long exact homology-sequence API given by the connecting map
  `ShortComplex.ShortExact.δ` together with the exactness theorems
  `ShortComplex.ShortExact.homology_exact₁`, `ShortComplex.ShortExact.homology_exact₂`, and
  `ShortComplex.ShortExact.homology_exact₃`.
- bridge/view: the remark's displayed groups are identified with the degree-`n` homology of the
  Hom complex by `(CochainComplex.HomComplex.homologyAddEquiv L I n).trans homAddEquiv`.
- companion API: the connecting morphism `ShortComplex.ShortExact.δ` and the exact five-term
  segment `HomologicalComplex.HomologySequence.composableArrows₅_exact`.

Source/core/bridge triage:
- `source-facing`: the remark's displayed long exact sequence of groups
  `Hom_{K(\operatorname{Mod}^{dg}(\mathcal A, d))}(\mathcal M, \mathcal I[n])`.
- `core/canonical`: `ShortComplex.ShortExact.homologySequence`.
- `bridge/view`: the Hom-complex cohomology equivalence
  `(CochainComplex.HomComplex.homologyAddEquiv L I n).trans homAddEquiv`. -/

section

variable {C : Type u} [Category.{v} C] [Preadditive C]
variable (L I : CochainComplex C ℤ) (n : ℤ)

/-
Remark 24.25.3: the displayed groups
`Hom_{K(\operatorname{Mod}^{dg}(\mathcal A, d))}(\mathcal M, \mathcal I[n])`
are the canonical degree-`n` homology groups of the Hom complex, via the upstream composite from
`H^n(Hom^•(L, I))` to morphisms `L ⟶ I⟦n⟧` in the homotopy category. Combined with the canonical
long exact cohomology sequence for a short exact sequence of complexes, this is the source-facing
owner package behind the remark's long exact sequence, without appealing to admissibility of the
original short exact sequence in the homotopy category. -/
#check (CochainComplex.HomComplex.homologyAddEquiv L I n).trans homAddEquiv

end

section

variable {C : Type u} [Category.{v} C] [Abelian C]
variable {S : ShortComplex (CochainComplex C ℤ)} (hS : S.ShortExact) (n : ℤ)

/-
Remark 24.25.3: once the Hom-complex short exact sequence is available, the source-facing long
exact sequence is owned by the canonical connecting map `ShortComplex.ShortExact.δ` together with
the exactness theorems `ShortComplex.ShortExact.homology_exact₁`,
`ShortComplex.ShortExact.homology_exact₂`, and `ShortComplex.ShortExact.homology_exact₃`. -/
recall ShortComplex.ShortExact.homology_exact₁
recall ShortComplex.ShortExact.homology_exact₂
recall ShortComplex.ShortExact.homology_exact₃

/- Bridge/view: the displayed cohomology window is the cochain-complex specialization of the
canonical five-term fragment of that long exact sequence. -/
recall composableArrows₅

/- Companion recall: the displayed connecting morphism is the canonical boundary map
`ShortComplex.ShortExact.δ` in that long exact sequence. -/
recall ShortComplex.ShortExact.δ

/- Companion recall: the displayed five-term segment is exact by the canonical owner theorem
`HomologicalComplex.HomologySequence.composableArrows₅_exact`. -/
#check (composableArrows₅_exact hS n (n + 1) (up_mk n (n + 1) rfl) :
    (composableArrows₅ hS n (n + 1) (up_mk n (n + 1) rfl)).Exact)

end

end CategoryTheory
