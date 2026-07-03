import stacks_project.Chap15.Definition_15_105_1

-- Declarations for this item will be appended below by the statement pipeline.

open scoped TensorProduct
open Algebra.TensorProduct

universe u v w

section

variable {A : Type u} {A' : Type v} {B : Type w}
variable [CommRing A] [CommRing A'] [CommRing B] [Algebra A B] [Algebra A A']

local notation "B'" => A' ⊗[A] B

/- Domain-style sampling for weakly étale base change:
- primary domain: commutative algebra of flat ring maps and weakly étale morphisms under tensor
  base change;
- source-facing layer: part `(1)` is the tensor-square flatness clause in the weakly étale
  criterion after base change;
- core/canonical owner: the chapter-local ring-map owner `Algebra.IsWeaklyEtale`;
- sampled bridge API: `RingHom.Flat.tensorProductMap` for tensor-product flatness and
  `Algebra.TensorProduct.cancelBaseChange` / `assoc` for the canonical identification of the
  base-changed tensor square;
- primitive data: flatness of `lmul' A`;
- derived API: flatness of `lmul' A'` and the owner theorem `Algebra.IsWeaklyEtale.baseChange`.
-/

namespace Algebra

-- Proof sketch: identify the multiplication map
-- `(A' ⊗[A] B) ⊗[A'] (A' ⊗[A] B) → A' ⊗[A] B` with the base change of
-- `B ⊗[A] B → B` along `A → A'`, and then apply flat base change from Lemma `10.39.7`.
/-- Lemma 15.105.7 (1): if the multiplication map `B ⊗[A] B → B` is flat, then the multiplication
map `(A' ⊗[A] B) ⊗[A'] (A' ⊗[A] B) → A' ⊗[A] B` is flat. -/
theorem tensorSquareMul_flat_baseChange
    (hflatMul : (lmul' A : B ⊗[A] B →ₐ[A] B).Flat) :
    let _ : Algebra (B' ⊗[A'] B') B' := (lmul' A').toAlgebra
    Module.Flat (B' ⊗[A'] B') B' := by
  sorry

-- Proof sketch: flatness of the structure map after base change is canonical, and part `(1)`
-- gives the tensor-square multiplication clause.
namespace IsWeaklyEtale

/-- Lemma 15.105.7 (2): if `A → B` is weakly étale, then the base-changed map
`A' → A' ⊗[A] B` is weakly étale. -/
theorem baseChange (hAB : IsWeaklyEtale A B) : IsWeaklyEtale A' B' := by
  sorry

end IsWeaklyEtale

/- Bridge/view: weakly étaleness is preserved under tensor base change. -/
attribute [instance] IsWeaklyEtale.baseChange

end Algebra

end
