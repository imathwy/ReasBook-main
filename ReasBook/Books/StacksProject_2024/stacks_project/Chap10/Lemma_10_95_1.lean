import Mathlib
import StacksProject_2024.stacks_project.Chap10.Proposition_10_89_5

-- Declarations for this item will be appended below by the statement pipeline.

open scoped TensorProduct

universe u v w

namespace Module

section

variable {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S]
variable {M : Type w} [AddCommGroup M] [Module R M]
variable [Module.FaithfullyFlat R S]

/- Source/core/bridge triage:
* source-facing: descent of the Mittag-Leffler property along a faithfully flat base change;
* core/canonical owner: `Module.MittagLeffler`, sampled via
  `mittagLeffler_iff_tensorProduct_piRight_injective`,
  `TensorProduct.piRightHom`, and `Module.FaithfullyFlat.lTensor_injective_iff_injective`;
* adjacent bridge theorem checked and rejected as the main owner reuse:
  `Module.mittagLeffler_restrictScalars_of_mittagLeffler_of_flat` from Lemma `10.89.11`, whose
  extra hypotheses `[MittagLeffler R S] [Module.Flat S M]` change the semantics of the present
  faithfully flat descent statement;
* bridge/view: compare the tensor-product-with-products map over `R` with its base change to `S`
  and reflect injectivity along the faithfully flat extension.
-/
-- Proof sketch: use the canonical injectivity criterion for `Module.MittagLeffler` from
-- Proposition `10.89.5`. For each family `(Q a)` of `R`-modules, reflect injectivity of
-- `TensorProduct.piRightHom R R M Q` from its left tensor with `S` via
-- `Module.FaithfullyFlat.lTensor_injective_iff_injective`; after the standard tensor-associativity
-- and product-compatibility identifications, the resulting map is exactly the `S`-linear
-- `TensorProduct.piRightHom` for `S ⊗[R] M`, which is injective by the assumed
-- `Module.MittagLeffler S (S ⊗[R] M)`.
/-- Lemma 10.95.1: if the faithfully flat base change `S ⊗[R] M` is a Mittag-Leffler `S`-module,
then `M` is a Mittag-Leffler `R`-module. -/
theorem mittagLeffler_of_mittagLeffler_tensorProduct_of_faithfullyFlat
    [MittagLeffler S (S ⊗[R] M)] :
    MittagLeffler R M := by
  sorry

end

end Module
