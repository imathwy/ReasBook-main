import Mathlib.Tactic.Recall
import StacksProject_2024.stacks_project.Chap20.Lemma_20_27_3

noncomputable section

namespace AlgebraicGeometry.RingedSpace

/- Domain-style sampling for Lemma 20.27.5:
- primary domain: the objectwise commutative square comparing the pullback-tensor comparison of
  Lemma `20.27.3` with the two canonical counits;
- sampled declarations:
  `modulePullbackDerivedTensor_existsComparison_commSq`,
  `CategoryTheory.CommSq`;
- owner abstraction:
  `source-facing`: the literal-complex specialization of the Chapter 20 comparison square;
  `core/canonical`: `modulePullbackDerivedTensor_existsComparison_commSq`;
  `bridge/view`: evaluation at `Kq := quotient.obj K` and `L := Q.obj M`.
- primitive data: the chosen comparison morphism from Lemma `20.27.3`, the two canonical counits,
  and the theorem-level underived bottom edge from the owner file;
- derived API: this item should reuse the owner existence theorem for the comparison square
  directly rather than restate it.

Source/core/bridge triage:
- `source-facing`: the objectwise square of Lemma `20.27.5`;
- `core/canonical`: `modulePullbackDerivedTensor_existsComparison_commSq`;
- `bridge/view`: the specialization from an arbitrary homotopy-category object and derived right
  factor to literal complexes `K` and `M`.
-/

/- Lemma 20.27.5 is recall-only: it is exactly the public existence theorem
`modulePullbackDerivedTensor_existsComparison_commSq` from Lemma `20.27.3`, specialized to
literal complexes via `Kq := quotient.obj K` and `L := Q.obj M`. -/
recall modulePullbackDerivedTensor_existsComparison_commSq

end AlgebraicGeometry.RingedSpace
