import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open ComplexShape
open HomologicalComplex.HomologySequence

universe v u

namespace CategoryTheory

/-
Domain-style sampling in the homology-sequence owner API:
- primitive owner data: `ShortComplex.ShortExact.δ`
- owner sequence object: `HomologicalComplex.HomologySequence.composableArrows₅`
- derived exactness pieces: `ShortComplex.ShortExact.homology_exact₁`,
  `ShortComplex.ShortExact.homology_exact₂`, `ShortComplex.ShortExact.homology_exact₃`
- owner exact five-term segment: `HomologicalComplex.HomologySequence.composableArrows₅_exact`

Lemma 12.13.6 is `bridge/view`: the chain-complex `ComplexShape.down ℤ` specialization of that
owner theorem, so the main entry should be direct specialized use of the owner theorem rather than
a parallel chapter-local theorem.
-/

variable {C : Type u} [Category.{v} C] [Abelian C]
variable {S : ShortComplex (ChainComplex C ℤ)} (hS : S.ShortExact) (i : ℤ)

/-
Lemma 12.13.6: a short exact sequence of chain complexes in an abelian category yields the
canonical exact homology segment
`H_i(A_•) ⟶ H_i(B_•) ⟶ H_i(C_•) ⟶ H_{i-1}(A_•) ⟶ H_{i-1}(B_•) ⟶ H_{i-1}(C_•)`,
with connecting morphism
`hS.δ i (i - 1) (down_mk i (i - 1) (sub_add_cancel i 1))`. This is exactly the owner theorem
`HomologicalComplex.HomologySequence.composableArrows₅_exact`, specialized to the chain-complex
shape `ComplexShape.down ℤ`. -/
#check (composableArrows₅_exact hS i (i - 1) (down_mk i (i - 1) (sub_add_cancel i 1)) :
    (composableArrows₅ hS i (i - 1) (down_mk i (i - 1) (sub_add_cancel i 1))).Exact)

end CategoryTheory
