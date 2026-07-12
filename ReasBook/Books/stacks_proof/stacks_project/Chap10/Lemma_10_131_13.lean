import Mathlib
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.

open scoped TensorProduct
open KaehlerDifferential

universe u v

section

variable (R : Type u) (S : Type v) [CommRing R] [CommRing S] [Algebra R S]

/- Domain-style sampling for Lemma 10.131.13:
- primary domain: Kähler differentials and their cotangent-ideal presentation for commutative
  `R`-algebras `S`;
- sampled owner declarations:
  `KaehlerDifferential`,
  `KaehlerDifferential.ideal`,
  `KaehlerDifferential.D_apply`,
  `KaehlerDifferential.submodule_span_range_eq_ideal`;
- best owner abstraction: `KaehlerDifferential R S`, canonically implemented as
  `(KaehlerDifferential.ideal R S).Cotangent`;
- primitive data: the kernel ideal `J := ideal R S` and its quotient map `J → J/J²`;
- derived API: the class formula `D_apply` and the explicit tensor representative for `a • db`.

Source/core/bridge triage:
- `source-facing`: the textbook `J/J²` presentation of `Ω[S⁄R]` and the tensor representative of
  `a • db`;
- `core/canonical`: `KaehlerDifferential R S`, `ideal R S`, and `D_apply`;
- `bridge/view`: the two companion theorems below translating the canonical owner into the tensor
  representative used in the source. -/

/- Lemma 10.131.13: if `J = ker(S ⊗[R] S → S)` is the kernel of the multiplication map, then the
module of Kähler differentials `Ω[S⁄R]` is canonically `J/J²`. In mathlib this identification is
built into the definition `KaehlerDifferential R S = (KaehlerDifferential.ideal R S).Cotangent`. -/
recall KaehlerDifferential

/- Companion recall: the ideal `J` in the cotangent description of `Ω[S⁄R]` is the kernel of the
multiplication map `S ⊗[R] S → S`. -/
recall KaehlerDifferential.ideal

/- Companion recall: the universal differential sends `b` to the class of `1 ⊗ b - b ⊗ 1`
in `J/J²`. -/
recall KaehlerDifferential.D_apply

namespace KaehlerDifferential

/-- The tensor `a ⊗ b - ab ⊗ 1` lies in the Kähler differential ideal `J`. -/
theorem tensor_sub_mul_tmul_one_mem_ideal (a b : S) :
    a ⊗ₜ[R] b - (a * b) ⊗ₜ[R] (1 : S) ∈ ideal R S := by
  simp [KaehlerDifferential.ideal, RingHom.mem_ker]

/-- In the cotangent presentation of `Ω[S⁄R]`, the element `a • db` is represented by
`a ⊗ b - ab ⊗ 1`. -/
theorem smul_D_apply (a b : S) :
    a • D R S b =
      (ideal R S).toCotangent
        ⟨a ⊗ₜ[R] b - (a * b) ⊗ₜ[R] (1 : S),
          tensor_sub_mul_tmul_one_mem_ideal R S a b⟩ := by
  rw [D_apply]
  change (ideal R S).toCotangent
      (a • ⟨1 ⊗ₜ[R] b - b ⊗ₜ[R] (1 : S), one_smul_sub_smul_one_mem_ideal R b⟩) = _
  congr
  ext
  simp [smul_sub, TensorProduct.smul_tmul', smul_eq_mul, mul_one]

end KaehlerDifferential

end
