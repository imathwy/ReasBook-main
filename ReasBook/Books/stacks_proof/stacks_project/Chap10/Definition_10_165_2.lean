import Mathlib
import StacksProject_2024.Chap10.Definition_10_37_11

-- Declarations for this item will be appended below by the statement pipeline.

open scoped TensorProduct

universe u v

namespace Algebra

/-- Definition 10.165.2: a commutative `k`-algebra `R` is geometrically normal over `k` if for
every field extension `K / k`, the base change `K ⊗[k] R` is a normal ring. By Lemma 10.165.1,
this is equivalent to the other usual tests for geometric normality. -/
@[stacks 0380]
class IsGeometricallyNormal (k : Type u) (R : Type v) [Field k] [CommRing R] [Algebra k R] :
    Prop where
  /-- Every scalar extension of a geometrically normal algebra to a field is a normal ring. -/
  isNormalRing_baseChange (K : Type (max u v)) [Field K] [Algebra k K] :
    IsNormalRing (K ⊗[k] R)

section

variable (k : Type u) [Field k]

/-- The ground field is geometrically normal over itself. -/
instance : IsGeometricallyNormal k k := by
  refine ⟨?_⟩
  intro K _ _
  let e : K ⊗[k] k ≃ₐ[k] K := TensorProduct.rid k k K
  letI : IsDomain (K ⊗[k] k) := Function.Injective.isDomain e.toRingHom e.injective
  letI : IsIntegrallyClosed (K ⊗[k] k) := IsIntegrallyClosed.of_equiv e.symm.toRingEquiv
  infer_instance

end

end Algebra
