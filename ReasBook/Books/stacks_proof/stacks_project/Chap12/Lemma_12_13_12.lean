import Mathlib
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.

open ComplexShape
open HomologicalComplex.HomologySequence

universe v u

namespace CategoryTheory

/- Domain-style sampling:
- primary domain: cohomology exact sequences attached to short exact sequences of cochain
  complexes, together with the shift identifications relating neighboring degrees;
- sampled owner declarations:
  `HomologicalComplex.HomologySequence.composableArrows₅`,
  `HomologicalComplex.HomologySequence.composableArrows₅_exact`,
  `HomologicalComplex.HomologySequence.mapComposableArrows₅`,
  `CochainComplex.ShiftSequence.shiftIso`;
- best owner abstraction for the main exactness statement: the generic homology-sequence owner
  `HomologicalComplex.HomologySequence.composableArrows₅_exact`, with the textbook cochain
  statement obtained by specialization to `ComplexShape.up ℤ`.

Source/core/bridge triage:
- `source-facing`: the cochain exact segment
  `H^i(A^•) ⟶ H^i(B^•) ⟶ H^i(C^•) ⟶ H^(i + 1)(A^•) ⟶ H^(i + 1)(B^•) ⟶ H^(i + 1)(C^•)`;
- `core/canonical`: `HomologicalComplex.HomologySequence.composableArrows₅_exact`;
- `bridge/view`: the `ComplexShape.up ℤ` specializations of
  `composableArrows₅_exact` and `mapComposableArrows₅`.

Primitive data are exactly the short exactness witness `hS : S.ShortExact`; the exact segment,
its functorial map under a morphism of short exact sequences, and the cochain shift comparison
are derived API from the owner declarations above.
-/

variable {C : Type u} [Category.{v} C] [Abelian C]
variable {S : ShortComplex (CochainComplex C ℤ)} (hS : S.ShortExact) (i : ℤ)

/- Lemma 12.13.12: a short exact sequence of cochain complexes in an abelian category yields the
canonical exact cohomology segment
`H^i(A^•) ⟶ H^i(B^•) ⟶ H^i(C^•) ⟶ H^(i + 1)(A^•) ⟶ H^(i + 1)(B^•) ⟶ H^(i + 1)(C^•)`,
with connecting morphism `hS.δ i (i + 1) (up_mk i (i + 1) rfl)`. This is exactly the owner
theorem `HomologicalComplex.HomologySequence.composableArrows₅_exact`, specialized to the
cochain shape `ComplexShape.up ℤ`. -/
#check (HomologicalComplex.HomologySequence.composableArrows₅_exact hS i (i + 1)
  (up_mk i (i + 1) rfl) :
    (composableArrows₅ hS i (i + 1) (up_mk i (i + 1) rfl)).Exact)

/- Functoriality companion: a morphism of short exact sequences of cochain complexes induces a
morphism between the corresponding exact cohomology segments in degree `i`. This is the
`ComplexShape.up ℤ` specialization of the owner map `mapComposableArrows₅`. -/
variable {S₁ S₂ : ShortComplex (CochainComplex C ℤ)} (φ : S₁ ⟶ S₂)
variable (hS₁ : S₁.ShortExact) (hS₂ : S₂.ShortExact)

#check (HomologicalComplex.HomologySequence.mapComposableArrows₅ φ hS₁ hS₂ i (i + 1)
  (up_mk i (i + 1) rfl) :
    composableArrows₅ hS₁ i (i + 1) (up_mk i (i + 1) rfl) ⟶
      composableArrows₅ hS₂ i (i + 1) (up_mk i (i + 1) rfl))

/- Shift-compatibility companion: the cohomology functor on cochain complexes carries the
canonical shift isomorphisms `H^i(K⟦n⟧) ≅ H^(i + n)(K)` used to identify the long exact sequence
of a shifted short exact sequence with the shifted long exact sequence. This is the source-facing
cochain owner `CochainComplex.ShiftSequence.shiftIso`. -/
recall CochainComplex.ShiftSequence.shiftIso

end CategoryTheory
