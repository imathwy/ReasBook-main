import Mathlib

/-
Domain-style sampling for Lemma 10.147.2:
- primary domain: integral closure and smooth/étale base change for tensor products.
- sampled owner declarations:
  `TensorProduct.toIntegralClosure`,
  `TensorProduct.toIntegralClosure_injective_of_flat`,
  `TensorProduct.toIntegralClosure_bijective_of_isLocalization`,
  `TensorProduct.toIntegralClosure_bijective_of_smooth`.
- best owner abstraction: the canonical comparison morphism `TensorProduct.toIntegralClosure`
  together with the owner theorem `TensorProduct.toIntegralClosure_bijective_of_smooth`.
- primitive-vs-derived split:
  primitive data: the commutative rings and algebra structures;
  derived API: bijectivity of the comparison map under extra hypotheses such as smoothness or
  étaleness.

Source/core/bridge triage:
- `source-facing`: the present étale specialization matching the Stacks lemma.
- `core/canonical`: `TensorProduct.toIntegralClosure_bijective_of_smooth`.
- `bridge/view`: the instance `[Algebra.Etale R S]` supplying the derived smoothness hypothesis. -/

-- Declarations for this item will be appended below by the statement pipeline.

universe u v w

namespace TensorProduct

section

variable {R : Type u} {S : Type v} {B : Type w}
variable [CommRing R] [CommRing S] [CommRing B]
variable [Algebra R S] [Algebra R B] [Algebra.Etale R S]

-- Proof sketch: `[Algebra.Etale R S]` provides `[Algebra.Smooth R S]`, so this is the direct
-- source-facing specialization of the canonical owner theorem
-- `TensorProduct.toIntegralClosure_bijective_of_smooth`.
/-- Lemma 10.147.2: if `R → S` is étale and `A = integralClosure R B`, then the canonical map
`S ⊗[R] A → integralClosure S (S ⊗[R] B)` is bijective, hence an isomorphism. -/
theorem toIntegralClosure_bijective_of_etale :
    Function.Bijective (toIntegralClosure R S B) :=
  TensorProduct.toIntegralClosure_bijective_of_smooth

end

end TensorProduct
