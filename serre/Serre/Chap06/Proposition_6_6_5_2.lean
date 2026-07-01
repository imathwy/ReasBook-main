import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open scoped MonoidAlgebra

universe u v

section

variable {A : Type u} [CommRing A]
variable {M : Type v} [Monoid M] [Finite M]

namespace MonoidAlgebra

-- Source/core/bridge triage:
-- * source-facing: Proposition 6-6.5-2 below, specialized to the complex group algebra `ℂ[G]`.
-- * core/canonical owner: `MonoidAlgebra.isIntegral_of_coeff_isIntegral`, which necessarily lives
--   in the commutative coefficient-ring layer because the finite-generation step runs through
--   `Algebra.adjoin ℤ coeffs`.
-- * primitive data: the finite monoid algebra ambient `A[M]`, an element `x : A[M]`, and the
--   coefficientwise integrality hypothesis `hx`.
-- * bridge/view: the center-subtype transport
--   `MonoidAlgebra.isIntegral_center_of_coeff_isIntegral`.
-- * derived API: Proposition 6-6.5-2 as the complex center specialization, and the downstream
--   center-valued corollaries.
/-- In a finite monoid algebra, coefficientwise integrality over `ℤ` implies integrality of the
whole element over `ℤ`. -/
theorem isIntegral_of_coeff_isIntegral (x : A[M]) (hx : ∀ m : M, IsIntegral ℤ (x m)) :
    IsIntegral ℤ x := by
  classical
  let coeffs : Set A := Set.range x
  let S : Subring A := Subring.closure coeffs
  have hS : Module.Finite ℤ S := by
    have hcoeffs : Module.Finite ℤ (Algebra.adjoin ℤ coeffs) :=
      Algebra.finite_adjoin_of_finite_of_isIntegral (Set.finite_range x) fun a ha ↦ by
        rcases ha with ⟨m, rfl⟩
        exact hx m
    let _ : Module.Finite ℤ (Algebra.adjoin ℤ coeffs) := hcoeffs
    exact Module.Finite.equiv (Subring.closureEquivAdjoinInt coeffs).toLinearEquiv.symm
  haveI : Module.Finite ℤ S := hS
  let xS : S[M] := by
    refine ⟨x.support, fun m ↦ ⟨x m, Subring.subset_closure ⟨m, rfl⟩⟩, ?_⟩
    intro m
    simp
  letI : Module.Finite ℤ S[M] := MonoidAlgebra.moduleFinite
  have hxS : IsIntegral ℤ xS := IsIntegral.of_finite ℤ xS
  have hmap : mapRingHom M S.subtype xS = x := by
    ext m
    simp [xS, mapRingHom_apply]
  exact hmap ▸ map_isIntegral_int (mapRingHom M S.subtype) hxS

/-- The center-valued form of `isIntegral_of_coeff_isIntegral`: a central monoid-algebra element
whose coefficients are integral over `ℤ` is itself integral over `ℤ`. -/
theorem isIntegral_center_of_coeff_isIntegral
    (u : Subalgebra.center A (A[M])) (hu : ∀ m : M, IsIntegral ℤ ((u : A[M]) m)) :
    IsIntegral ℤ u := by
  refine
    (isIntegral_algHom_iff
      ((Subalgebra.center A (A[M])).val.restrictScalars ℤ)
      Subtype.val_injective).1 ?_
  exact isIntegral_of_coeff_isIntegral (u : A[M]) hu

end MonoidAlgebra

variable {G : Type v} [Group G] [Finite G]

/-- Proposition 6-6.5-2: a central element of the complex group algebra `ℂ[G]` whose
coefficients are algebraic integers is itself integral over `ℤ`. -/
theorem isIntegral_complexGroupRingCenter_of_coeff_isIntegral
    (u : Subalgebra.center ℂ (ℂ[G])) (hu : ∀ s : G, IsIntegral ℤ ((u : ℂ[G]) s)) :
    IsIntegral ℤ u :=
  MonoidAlgebra.isIntegral_center_of_coeff_isIntegral u hu

end
