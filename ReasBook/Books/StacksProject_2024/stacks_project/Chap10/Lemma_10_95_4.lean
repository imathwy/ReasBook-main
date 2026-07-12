import Mathlib
import StacksProject_2024.Chap10.Definition_10_84_1

-- Declarations for this item will be appended below by the statement pipeline.

open scoped TensorProduct
open Algebra.TensorProduct

attribute [local instance high] Algebra.TensorProduct.leftAlgebra Algebra.toModule

universe u v w

section

variable {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S]
variable {M : Type w} [AddCommGroup M] [Module R M]

-- Proof sketch: choose countably many generators for `Q`, write each generator as a finite sum of
-- pure tensors, and let `P` be the submodule spanned by all module components appearing in those
-- sums. This spanning set is still countable, and every generator of `Q` lies in `P.baseChange S`,
-- hence the whole submodule `Q` is contained in `P.baseChange S`.
/-- Lemma 10.95.4: every countably generated `S`-submodule `Q` of the scalar extension
`S ⊗[R] M` is contained in the base change of a countably generated `R`-submodule `P ≤ M`. This
is the canonical Lean form of saying that the image of `P ⊗_R S → M ⊗_R S` contains `Q`. -/
theorem exists_countablyGenerated_submodule_whose_baseChange_contains
    {Q : Submodule S (S ⊗[R] M)}
    (hQ : Q.CountablyGenerated) :
    ∃ P : Submodule R M, P.CountablyGenerated ∧ Q ≤ P.baseChange S := sorry

end
