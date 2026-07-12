import StacksProject_2024.Chap10.Lemma_10_43_2

universe u v

open scoped TensorProduct
open Algebra
open Algebra.TensorProduct

section

variable {k : Type u} {R : Type v} [Field k] [CommRing R] [Algebra k R]

/- Lemma 10.43.3 (1): if `R` is geometrically reduced over `k`, then every localization of `R`
at a multiplicative subset is geometrically reduced over `k`. This is exactly
`isGeometricallyReduced_localization`. -/
recall isGeometricallyReduced_localization

-- Proof sketch: identify `K ⊗[k] R[X]` with
-- `(K ⊗[k] R)[X]` for an arbitrary field extension `K / k`. The tensor product `K ⊗[k] R` is
-- reduced by Lemma `10.43.5`, and polynomial rings over reduced commutative rings are reduced.
/-- Lemma 10.43.3 (2) (Tag 04KN): if `R` is geometrically reduced over `k`, then `R[X]` is
geometrically reduced over `k`. -/
@[stacks 04KN]
theorem isGeometricallyReduced_polynomial [IsGeometricallyReduced k R] :
    IsGeometricallyReduced k (Polynomial R) := by
  rw [isGeometricallyReduced_iff_forall_isReduced_tensorProduct]
  intro K _ _
  letI : IsReduced (K ⊗[k] R) := inferInstance
  letI : IsReduced (Polynomial (K ⊗[k] R)) := by
    let e := MvPolynomial.pUnitAlgEquiv.{max u v, 0} (K ⊗[k] R)
    letI : IsReduced (MvPolynomial PUnit (K ⊗[k] R)) := inferInstance
    exact isReduced_of_injective e.symm e.symm.injective
  let e : K ⊗[k] Polynomial R ≃ₐ[k] Polynomial (K ⊗[k] R) :=
    (congr (AlgEquiv.refl : K ≃ₐ[k] K) (polyEquivTensor k R)).trans <|
      (Algebra.TensorProduct.assoc k k k K R (Polynomial k)).symm.trans <|
        (polyEquivTensor k (K ⊗[k] R)).symm
  exact isReduced_of_injective e e.injective

instance [IsGeometricallyReduced k R] : IsGeometricallyReduced k (Polynomial R) :=
  isGeometricallyReduced_polynomial

end
