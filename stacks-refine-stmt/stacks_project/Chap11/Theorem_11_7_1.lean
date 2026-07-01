import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

namespace Subalgebra

section

variable {k : Type u} [Field k]
variable (A : CSA.{u, v} k) (B : Subalgebra k A)
variable [IsSimpleRing B]

/- Theorem 11.7.1 is `source-facing`: its public statements are about the canonical owner
abstraction `Subalgebra.centralizer`, so the results live on the `Subalgebra` owner namespace
rather than behind file-local wrapper names. The supporting `core/canonical` API is the
simple-module double-centralizer equivalence from Lemma 11.4.6 together with the tensor-product
simplicity bridge from Lemma 11.4.7, so no extra local wrapper is introduced here. -/
local notation "C" => centralizer k (B : Set A)

-- Proof sketch: choose a simple left `A`-module `M`, let `L := Module.End A M`, and rewrite the
-- centralizer of `B` as the endomorphism ring of `M` as a right `B ⊗[k] Lᵐᵒᵖ`-module. The tensor
-- product algebra is simple by the earlier tensor-product lemma, so the endomorphism ring is
-- simple by the finite-module structure theorem for simple algebras.
/-- Theorem 11.7.1 (1): if `A` is a finite central simple `k`-algebra and `B` is a simple
subalgebra of `A`, then the centralizer of `B` in `A` is simple. -/
theorem isSimpleRing_centralizer :
    IsSimpleRing C := sorry

-- Proof sketch: with the same simple `A`-module `M` and `L := Module.End A M`, identify
-- `B ⊗[k] Lᵐᵒᵖ` and the centralizer `C` with matrix algebras over opposite division rings, then
-- compare the resulting dimension formulas from the simple-module structure theorem.
/-- Theorem 11.7.1 (2): if `C` is the centralizer of a simple subalgebra `B ⊆ A`, then
`[A : k] = [B : k] [C : k]`. -/
theorem finrank_mul_finrank_centralizer :
    Module.finrank k A =
      Module.finrank k B * Module.finrank k C := sorry

-- Proof sketch: apply the dimension formula again to the inclusion `C ⊆ A`, where `C` is the
-- centralizer of `B`, to show that the centralizer of `C` has the same `k`-dimension as `B`;
-- combine this with the obvious inclusion `B ≤ C_A(C)` to deduce equality.
/-- Theorem 11.7.1 (3): if `C` is the centralizer of a simple subalgebra `B ⊆ A`, then the
centralizer of `C` in `A` is exactly `B`. -/
theorem centralizer_centralizer_eq :
    centralizer k (C : Set A) = B := sorry

end

end Subalgebra
