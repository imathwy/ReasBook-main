import Mathlib
import stacks_project.Chap10.Definition_10_88_7

-- Declarations for this item will be appended below by the statement pipeline.

universe u v w x

namespace Module

section

variable {R : Type u} [CommRing R]
variable {M : Type v} [AddCommGroup M] [Module R M]

-- Proof sketch: for the forward implication, choose a directed colimit presentation of `M` by
-- finitely presented modules with eventual factorization and reduce injectivity to the finitely
-- presented case using Proposition `10.89.3`. For the converse, test the injectivity hypothesis on
-- the families built from kernels of tensor maps out of finitely presented modules and use Lemma
-- `10.89.4`, Lemma `10.88.3`, and Proposition `10.88.6` to recover the eventual domination
-- condition in a finitely presented presentation of `M`.
/-- Proposition 10.89.5: an `R`-module `M` is Mittag-Leffler if and only if for every family
`(Q α)`, the canonical map
`M ⊗[R] (∀ α, Q α) → ∀ α, M ⊗[R] Q α` is injective. -/
theorem mittagLeffler_iff_tensorProduct_piRight_injective :
    MittagLeffler R M ↔
      ∀ (A : Type w) (Q : A → Type x) [∀ a, AddCommGroup (Q a)] [∀ a, Module R (Q a)],
        Function.Injective (TensorProduct.piRightHom R R M Q) := sorry

end

end Module
