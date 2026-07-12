import Mathlib.Algebra.Homology.HomotopyCategory.HomComplexCohomology
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open ComplexShape
open CochainComplex.HomComplex
open CochainComplex.HomComplex.Cocycle
open CochainComplex.HomComplex.CohomologyClass

universe u

section

variable {A : Type u} [Ring A]

local notation "DGMod" => CochainComplex (ModuleCat A) ℤ

variable (M Avee : DGMod) (k : ℤ)

/- Lemma 22.19.3 (1): in the canonical cochain-complex model for differential graded
`A`-modules, morphisms `M ⟶ A^\vee[k]` identify with degree-`k` cocycles in the dual Hom complex
`Hom^•(M, A^\vee)`. The source-facing bridge is exactly the canonical cocycle owner
`CochainComplex.HomComplex.Cocycle.equivHomShift`, so this item records a direct recall of that
owner rather than a duplicate local alias. -/
recall equivHomShift

/- Lemma 22.19.3 (2): the degree-`k` homology of the dual Hom complex `Hom^•(M, A^\vee)`
identifies canonically with morphisms from `M` to `A^\vee[k]` in the homotopy category. As in the
other Chapter 20/21/24 Hom-complex bridge files, the faithful refined surface is the direct
canonical composite `(homologyAddEquiv M Avee k).trans homAddEquiv`, not a duplicate local alias
for that composite. -/
#check (homologyAddEquiv M Avee k).trans homAddEquiv

end
