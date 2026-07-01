import Mathlib
import stacks_project.Chap11.Theorem_11_7_1

-- Declarations for this item will be appended below by the statement pipeline.

open scoped TensorProduct
open Algebra.TensorProduct

universe u v

namespace Subalgebra

section

variable {k : Type u} [Field k]
variable (A : CSA.{u, v} k) (B : Subalgebra k A)

local notation "C" => centralizer k (B : Set A)

private theorem centralizer_commutes (b : B) (c : C) :
    Commute (b : A) (c : A) := by
  change (b : A) * (c : A) = (c : A) * (b : A)
  exact c.2 b b.2

variable [IsSimpleRing B] [Algebra.IsCentral k B]

/- Domain sampling for Lemma 11.7.2.
- primary domain: tensor products of central simple algebras and centralizers of subalgebras;
- inspected owner declarations:
  `Subalgebra.finrank_mul_finrank_centralizer`,
  `Subalgebra.centralizer_centralizer_eq`,
  `Algebra.TensorProduct.lift`,
  `Algebra.TensorProduct.lift_tmul`;
- best owner abstraction: `Subalgebra.centralizer` on the subalgebra side, together with the
  canonical tensor-product multiplication map given directly by `Algebra.TensorProduct.lift`;
- primitive data: the subalgebra `B` and its centralizer `C_A(B)`;
- derived API: bijectivity of the canonical multiplication map and the resulting algebra
  equivalence;
- layer classification:
  `source-facing`: the algebra equivalence `B ⊗[k] C_A(B) ≃ₐ[k] A`;
  `core/canonical`: `Subalgebra.centralizer` and `Algebra.TensorProduct.lift`;
  `bridge/view`: the bijectivity theorem upgrading the canonical lift to an equivalence. -/

/- Lemma 11.7.2 is a `bridge/view` item: the source-facing statement is an explicit algebra
equivalence `B ⊗[k] C_A(B) ≃ₐ[k] A`, while the core owner map is the canonical tensor-product lift
`Algebra.TensorProduct.lift B.val C.val ...`. -/
-- Proof sketch: Theorem 11.7.1 gives the dimension identity
-- `[A : k] = [B : k] [C_A(B) : k]`, while Lemma 11.4.7 shows that `B ⊗[k] C_A(B)` is simple
-- because `B` is central simple over `k`. The canonical multiplication map is therefore injective,
-- and the dimension equality forces surjectivity.
/-- Lemma 11.7.2, owner form: the canonical multiplication map
`B ⊗[k] Subalgebra.centralizer k (B : Set A) →ₐ[k] A` is bijective. -/
theorem centralizerTensorProduct_bijective :
    Function.Bijective
      (lift B.val (centralizer k (B : Set A)).val (centralizer_commutes A B)) := sorry

/-- Lemma 11.7.2: if `A` is a finite central simple `k`-algebra and `B` is a simple central
`k`-subalgebra of `A`, then the canonical multiplication map identifies
`B ⊗[k] Subalgebra.centralizer k (B : Set A)` with `A`. -/
noncomputable def centralizerTensorProductAlgEquiv :
    B ⊗[k] C ≃ₐ[k] A :=
  AlgEquiv.ofBijective
    (lift B.val (centralizer k (B : Set A)).val (centralizer_commutes A B))
    (centralizerTensorProduct_bijective A B)

@[simp]
theorem centralizerTensorProductAlgEquiv_tmul (b : B) (c : C) :
    centralizerTensorProductAlgEquiv A B (b ⊗ₜ[k] c) = (b : A) * c := by
  simp [centralizerTensorProductAlgEquiv]

end

end Subalgebra
