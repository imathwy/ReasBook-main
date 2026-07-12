import Mathlib
import StacksProject_2024.Chap10.Definition_10_42_1
import StacksProject_2024.Chap10.Lemma_10_43_5

-- Declarations for this item will be appended below by the statement pipeline.

open scoped TensorProduct
open Algebra

universe u v w

/-
Domain triage:
- `source-facing`: the main lemma is reducedness of `K ⊗[k] S` for a reduced `k`-algebra `S` and a
  Stacks-separable field extension `K / k`.
- `core/canonical`: the owner abstraction for the field-extension side is
  `Algebra.IsGeometricallyReduced k K`.
- `bridge/view`: the geometric-reducedness consequence is derived from the source-facing tensor
  product lemma by commuting `AlgebraicClosure k ⊗[k] K`.

Primitive data are the reduced algebra `S` and the separable extension `K / k`; geometric
reducedness of `K` is derived API, not primitive data.
-/

section

variable {k : Type u} {K : Type v} {S : Type w}
variable [Field k] [Field K] [CommRing S] [Algebra k K] [Algebra k S]

/-- Lemma 10.43.6 (Tag 030U): if `S` is a reduced `k`-algebra and `K / k` is separable in the
sense of Definition 10.42.1(2), then the base change `K ⊗[k] S` is reduced. By
`Lemma_10_44_3`, this also applies to separably generated extensions. -/
@[stacks 030U]
theorem Lemma_10_43_6
    [IsReduced S]
    [IsSeparableOver k K] :
    IsReduced (K ⊗[k] S) := by
  sorry

end

section

variable {k : Type u} {K : Type v}
variable [Field k] [Field K] [Algebra k K]

/-- A field extension that is separable in the sense of Definition `10.42.1 (2)` is geometrically
reduced over the base field. -/
theorem isGeometricallyReduced_of_isSeparableOver
    [IsSeparableOver k K] :
    IsGeometricallyReduced k K := by
  refine ⟨?_⟩
  let e : AlgebraicClosure k ⊗[k] K ≃ₐ[k] K ⊗[k] AlgebraicClosure k :=
    Algebra.TensorProduct.comm k (AlgebraicClosure k) K
  letI : IsReduced (K ⊗[k] AlgebraicClosure k) := Lemma_10_43_6
  exact isReduced_of_injective e.toRingHom e.injective

@[instance low] instance [IsSeparableOver k K] : IsGeometricallyReduced k K :=
  isGeometricallyReduced_of_isSeparableOver

end
