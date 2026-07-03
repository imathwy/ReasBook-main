import Mathlib
import StacksProject_2024.Chap15.Definition_15_105_1

-- Declarations for this item will be appended below by the statement pipeline.

open scoped TensorProduct
open Algebra.TensorProduct

universe u v w

section

variable {A : Type u} {B : Type v} [CommRing A] [CommRing B] [Algebra A B]
variable {N : Type w} [AddCommGroup N] [Module B N] [Module A N] [IsScalarTower A B N]

/- Domain triage:
- primary domain: commutative algebra of flat modules and the tensor-square criterion for weakly
  étale morphisms;
- source-facing layer: this Stacks lemma transferring flatness of a module from the base ring `A`
  to the algebra `B` under flatness of the multiplication map `B ⊗[A] B → B`;
- core/canonical owners: `Module.Flat`, `Module.Flat.baseChange`, `Module.Flat.trans`,
  `Algebra.IsWeaklyEtale`, and `(lmul' A).Flat`;
- bridge/view: the owner-level companion `Module.Flat.of_isWeaklyEtale`, obtained by feeding the
  tensor-square flatness field of `Algebra.IsWeaklyEtale A B` into the source-facing theorem.

The numbered theorem remains source-facing: there is no exact upstream owner theorem with this
interface, so the refinement is to keep the textbook statement while exposing the direct
owner-facing bridge separately.
-/

-- Proof sketch: tensoring a short exact sequence of `B`-modules with `N` over `A` is exact
-- because `N` is `A`-flat. Reinterpret this as extension of scalars from `B` to `B ⊗[A] B`,
-- and then descend exactness back along the flat multiplication map
-- `B ⊗[A] B → B`, so tensoring over `B` with `N` is exact.
/-- Lemma 15.105.2: if the multiplication map `B ⊗[A] B → B` is flat and `N` is flat as an
`A`-module, then `N` is flat as a `B`-module. -/
theorem flat_of_flat_base_and_flat_tensorSquareMultiplication
    (hflatMul : (lmul' A : B ⊗[A] B →ₐ[A] B).Flat)
    (hflatN : Module.Flat A N) :
    Module.Flat B N := sorry

/-- Bridge/view: over a weakly étale map `A → B`, every `A`-flat `B`-module is `B`-flat. -/
theorem Module.Flat.of_isWeaklyEtale [Algebra.IsWeaklyEtale A B]
    (hflatN : Module.Flat A N) :
    Module.Flat B N :=
  flat_of_flat_base_and_flat_tensorSquareMultiplication
    ‹Algebra.IsWeaklyEtale A B›.flat_tensorSquareMultiplication hflatN

end
