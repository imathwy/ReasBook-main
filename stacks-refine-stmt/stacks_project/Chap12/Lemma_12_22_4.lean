import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open HomologicalComplex.HomologySequence

universe v u

namespace CategoryTheory

/-
Domain-style sampling for Lemma 12.22.4:
- primary domain: periodic homology exact sequences for differential objects in an abelian
  category, realized in this chapter as one-object homological complexes;
- sampled owner declarations:
  `HomologicalComplex.HomologySequence.composableArrows₅`,
  `HomologicalComplex.HomologySequence.composableArrows₅_exact`,
  `ShortComplex.ShortExact.homology_exact₁`,
  `ShortComplex.ShortExact.homology_exact₂`,
  `ShortComplex.ShortExact.homology_exact₃`;
- best owner abstraction: the canonical five-term homology segment
  `HomologicalComplex.HomologySequence.composableArrows₅_exact`, specialized to the one-object
  shape `ComplexShape.refl PUnit`;
- primitive data: a short exact sequence `hS : S.ShortExact` of one-object homological complexes;
- derived API: the periodic exact segment and its three consecutive exactness pieces.

Source/core/bridge triage:
- `source-facing`: the periodic homology segment attached to a short exact sequence of
  differential objects;
- `core/canonical`: `HomologicalComplex.HomologySequence.composableArrows₅_exact`;
- `bridge/view`: the specialization to `ComplexShape.refl PUnit`, using the Chapter 12
  identification of differential objects with one-object homological complexes.

No local exact-sequence theorem is needed here: the source statement is exactly this owner
specialization. -/

variable {C : Type u} [Category.{v} C] [Abelian C]
variable {S : ShortComplex (HomologicalComplex C (ComplexShape.refl PUnit.{1}))}
  (hS : S.ShortExact)

/- Lemma 12.22.4: a short exact sequence of differential objects in an abelian category yields
the exact periodic homology segment
`H(A, d) ⟶ H(B, d) ⟶ H(C, d) ⟶ H(A, d) ⟶ H(B, d) ⟶ H(C, d)`.

This is the `ComplexShape.refl PUnit` specialization of the canonical owner declaration
`HomologicalComplex.HomologySequence.composableArrows₅_exact`. -/
#check (composableArrows₅_exact hS PUnit.unit PUnit.unit rfl :
  (composableArrows₅ hS PUnit.unit PUnit.unit rfl).Exact)

end CategoryTheory
