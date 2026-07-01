import Mathlib.Tactic.Recall
import stacks_project.Chap15.«15_96_5_1»

-- Declarations for this item will be appended below by the statement pipeline.

/- Domain-style sampling for 20.55.7.1:
- primary domain: connecting-morphism naturality for short exact sequences of cochain complexes in
  an abelian category, specialized to the Bockstein square;
- sampled owner declarations:
  `HomologicalComplex.HomologySequence.δ_naturality`,
  `ShortComplex.SnakeInput.naturality_δ`,
  `CategoryTheory.CommSq`,
  `bockstein_factorization_naturality`;
- best owner abstraction:
  `source-facing`: the Bockstein factorization square in degree `i ⟶ i + 1`;
  `core/canonical`: `HomologicalComplex.HomologySequence.δ_naturality`;
  `bridge/view`: the specialization `ComplexShape.up_mk i (i + 1) rfl`;
- primitive data vs derived API: the primitive inputs are the short exact rows and their morphism
  `φ`; the displayed Bockstein square is derived API already owned upstream by
  `bockstein_factorization_naturality`, so this file should recall that owner directly instead of
  restating the same content as a parallel equality theorem. -/

/- 20.55.7.1: the displayed factorization of the Bockstein map through
`H^(i + 1)(M ⊗^L \mathcal I^{i + 1})` is exactly the previously formalized source-facing theorem
`bockstein_factorization_naturality`, itself the `j = i + 1` specialization of the naturality of
the connecting morphism for a morphism of short exact sequences of cochain complexes. In the
cohomology-of-sheaves situation, the upper boundary is `δ`, the lower boundary is the diagonal
Bockstein map `β`, and the vertical morphism is induced by
`\mathcal I^{i + 1} → \mathcal I^{i + 1} / \mathcal I^{i + 2}`. -/
recall bockstein_factorization_naturality
