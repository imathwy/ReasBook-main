import Mathlib.Tactic.Recall
import ConvexAnalysis_Rockafellar_1970.Chap04.Theorem_20_0_1
import ConvexAnalysis_Rockafellar_1970.Chap04.Corollary_20_0_2

-- Declarations for this item will be appended below by the statement pipeline.

/-!
Source/core/bridge triage for this item.

- `source-facing`: Corollary 20.0.3 packages the fully polyhedral specialization of the
  conjugate-of-sum formula together with the corresponding attainment statement.
- `core/canonical`: within Chapter 20.0, the source-facing owner declarations already exist as
  `convexConjugate_sum_eq_finiteInfimalConvolution_of_polyhedral_domNonempty`
  and
  `exists_sum_eq_finiteInfimalConvolution_conjugates_of_polyhedral_domNonempty`.
  Both owners live directly on the chapter `WithBotTop` codomain layer at the same scalar-generic
  finite-dimensional pairing-space abstraction, so this recall node does not need any
  `EReal`-bridge restatement.
  The broader Chapter 20.1 theorems remain upstream support for those owners, not the public
  declarations recalled here.
- `bridge/view`: this file is a recall node only; it introduces no second owner-level API and
  should reuse the direct Chapter 20.0 owners rather than skip to the more general 20.1 layer.

Domain-style sampling used here:
- `convexConjugate_sum_eq_finiteInfimalConvolution_of_polyhedral_domNonempty`;
- `exists_sum_eq_finiteInfimalConvolution_conjugates_of_polyhedral_domNonempty`;
- chapter-level `WithBotTop` codomain owner surfaces for conjugate-of-sum and attainment.

Primitive data vs derived API:
- no new primitive data belongs to this item;
- the source content is exactly the pair of direct Chapter 20.0 owners recalled below.

Layer target: `bridge/view`, since the mathematical content is already owned upstream in the
immediately preceding Chapter 20.0 items and this file should recall those direct owners rather
than restate them or bypass them with a more general upstream theorem pair.
-/

/- Corollary 20.0.3 recalls the direct Chapter 20.0 owner theorem for the all-polyhedral
conjugate-of-sum formula. -/
recall
  convexConjugate_sum_eq_finiteInfimalConvolution_of_polyhedral_domNonempty

/- Corollary 20.0.3 also recalls the matching Chapter 20.0 attainment statement for the finite
infimal convolution of the conjugates. -/
recall
  exists_sum_eq_finiteInfimalConvolution_conjugates_of_polyhedral_domNonempty
