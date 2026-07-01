import Mathlib
import Mathlib.Tactic.Recall
import stacks_project.Chap10.Lemma_10_43_5

-- Declarations for this item will be appended below by the statement pipeline.

open AlgebraicGeometry CategoryTheory Limits CommRingCat
open scoped TensorProduct

/- Definition 10.43.1 (Tag 030S): the canonical notion of a geometrically reduced `k`-algebra is
`Algebra.IsGeometricallyReduced`. -/
recall Algebra.IsGeometricallyReduced

namespace Algebra

universe u v

local instance :
    ObjectProperty.IsClosedUnderIsomorphisms (IsReduced : ObjectProperty Scheme) :=
  ⟨fun {X Y} e h ↦ by
    letI : IsReduced X := h
    exact isReduced_of_isOpenImmersion e.inv⟩

section

variable {k : Type u} {S : Type v} [Field k] [CommRing S] [Algebra k S]

/-- Definition 10.43.1 (Tag 030S): the Stacks Project condition that every field extension
`K / k` yields a reduced base change `K ⊗[k] S` is equivalent to the canonical mathlib class
`Algebra.IsGeometricallyReduced k S`. -/
@[stacks 030S]
theorem isGeometricallyReduced_iff_forall_isReduced_tensorProduct
    :
    IsGeometricallyReduced k S ↔
      ∀ (K : Type u) [Field K] [Algebra k K], IsReduced (K ⊗[k] S) := by
  rw [isGeometricallyReduced_iff]
  constructor
  · intro h K _ _
    letI : IsGeometricallyReduced k S := ⟨h⟩
    exact isReduced_tensorProduct_of_geometricallyReduced
  · intro h
    exact h (AlgebraicClosure k)

end

section

variable {k S : Type u} [Field k] [CommRing S] [Algebra k S]

/-- Companion bridge for Definition 10.43.1: on affine schemes over a field, the scheme-theoretic
notion of geometric reducedness agrees with `Algebra.IsGeometricallyReduced`. -/
theorem geometricallyReduced_iff_isGeometricallyReduced
    :
    GeometricallyReduced (Spec.map (CommRingCat.ofHom (algebraMap k S))) ↔
      IsGeometricallyReduced k S := by
  let f : Spec (of S) ⟶ Spec (of k) := Spec.map (CommRingCat.ofHom (algebraMap k S))
  change GeometricallyReduced f ↔ IsGeometricallyReduced k S
  rw [geometricallyReduced_iff, geometrically_iff_of_commRing_of_isClosedUnderIsomorphisms]
  constructor
  · intro h
    rw [isGeometricallyReduced_iff_forall_isReduced_tensorProduct]
    intro K _ _
    let e := pullbackSpecIso k S K
    let e' : K ⊗[k] S ≃ₐ[k] S ⊗[k] K := Algebra.TensorProduct.comm k K S
    letI : IsReduced (pullback f (Spec.map (CommRingCat.ofHom (algebraMap k K)))) := h K
    have hTensor : IsReduced (S ⊗[k] K) := by
      have hSpec : IsReduced (Spec (of (S ⊗[k] K))) := isReduced_of_isOpenImmersion e.inv
      exact (affine_isReduced_iff (of (S ⊗[k] K))).mp hSpec
    exact isReduced_of_injective e'.toRingHom e'.injective
  · intro h K _ _
    let e := pullbackSpecIso k S K
    let e' : K ⊗[k] S ≃ₐ[k] S ⊗[k] K := Algebra.TensorProduct.comm k K S
    have hReduced : IsReduced (S ⊗[k] K) := by
      let _ : IsReduced (K ⊗[k] S) :=
        (isGeometricallyReduced_iff_forall_isReduced_tensorProduct.mp h) K
      exact isReduced_of_injective e'.symm.toRingHom e'.symm.injective
    letI : IsReduced (Spec (of (S ⊗[k] K))) :=
      (affine_isReduced_iff (of (S ⊗[k] K))).mpr hReduced
    exact isReduced_of_isOpenImmersion e.hom

end

section

variable {k : Type u} [Field k]

/-- A field is geometrically reduced over itself. -/
instance : IsGeometricallyReduced k k := by
  rw [isGeometricallyReduced_iff]
  let e : AlgebraicClosure k ⊗[k] k ≃ₐ[k] AlgebraicClosure k :=
    Algebra.TensorProduct.rid k k (AlgebraicClosure k)
  exact isReduced_of_injective e.toRingHom e.injective

end

end Algebra
