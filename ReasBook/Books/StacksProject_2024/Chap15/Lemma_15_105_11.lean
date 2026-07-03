import stacks_project.Chap15.Lemma_15_105_7
import stacks_project.Chap15.Lemma_15_105_10

-- Declarations for this item will be appended below by the statement pipeline.

open scoped TensorProduct
open Algebra.TensorProduct

namespace Algebra
namespace IsWeaklyEtale

universe u v w

section

variable {A : Type u} {B : Type v} {C : Type w}
variable [CommRing A] [CommRing B] [CommRing C]
variable [Algebra A B] [Algebra A C] [Algebra B C] [IsScalarTower A B C]

attribute [local instance] TensorProduct.rightAlgebra

/- Domain triage:
- primary domain: commutative algebra of weakly étale ring maps in an algebra tower;
- source-facing layer: the Stacks closure lemma asserting that in a tower `A → B → C`, if both
  `A → B` and `A → C` are weakly étale, then so is `B → C`;
- core/canonical owners sampled for this file: `Algebra.IsWeaklyEtale`,
  `Algebra.IsWeaklyEtale.baseChange`, `Algebra.IsWeaklyEtale.of_faithfullyFlat`, and the
  canonical tensor-product map `Algebra.TensorProduct.lift`;
- primitive data: the two weakly étale owner facts on `A → B` and `A → C`;
- derived API: the base-changed weakly étale fact on `B → B ⊗[A] C`, faithful flatness of
  `C → B ⊗[A] C`, and the resulting owner fact on `B → C`.

This item remains source-facing. Its canonical proof route is the owner chain
`Algebra.IsWeaklyEtale.baseChange` followed by `Algebra.IsWeaklyEtale.of_faithfullyFlat`, with the
tensor-product map `C → B ⊗[A] C` handled as the split flat base change of `A → B`.
-/

-- Proof sketch: base change `A → C` along `A → B` to obtain the owner fact
-- `IsWeaklyEtale B (B ⊗[A] C)`. The base-changed map `C → B ⊗[A] C` is flat because `A → B` is
-- flat, and it has a retraction given by tensor-product multiplication, hence it is faithfully
-- flat. Then descend weak étaleness from `B → B ⊗[A] C` to `B → C` using the owner theorem
-- `Algebra.IsWeaklyEtale.of_faithfullyFlat`.
/-- Lemma 15.105.11: in a tower `A → B → C`, if both `A → B` and `A → C` are weakly étale, then
`B → C` is weakly étale. -/
theorem of_tower (hAB : IsWeaklyEtale A B) (hAC : IsWeaklyEtale A C) :
    IsWeaklyEtale B C := by
  sorry

end

end IsWeaklyEtale
end Algebra
