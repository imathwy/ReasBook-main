import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open scoped TensorProduct
open Algebra.TensorProduct

universe u v

section

variable {R : Type u} {S : Type v} [CommSemiring R] [CommSemiring S] [Algebra R S]

local notation "includeLeft" =>
  (Algebra.TensorProduct.includeLeft : S →ₐ[R] S ⊗[R] S)
local notation "includeRight" =>
  (Algebra.TensorProduct.includeRight : S →ₐ[R] S ⊗[R] S)
local notation "lmul'" =>
  (Algebra.TensorProduct.lmul' R : S ⊗[R] S →ₐ[R] S)

theorem algebra_isEpi_iff_includeLeft_eq_includeRight :
    Algebra.IsEpi R S ↔ includeLeft = includeRight := by
  constructor
  · intro h
    ext s
    simpa using ((Algebra.isEpi_iff_forall_one_tmul_eq R S).mp h s).symm
  · intro h
    exact (Algebra.isEpi_iff_forall_one_tmul_eq R S).mpr fun s ↦ by
      simpa using (congrArg (fun f ↦ f s) h).symm

theorem algebra_isEpi_iff_bijective_lmul :
    Algebra.IsEpi R S ↔ Function.Bijective lmul' := by
  constructor
  · intro h
    letI : Algebra.IsEpi R S := h
    refine ⟨?_, fun s ↦ ⟨1 ⊗ₜ[R] s, by simp⟩⟩
    simpa [lmul'_toLinearMap] using Algebra.injective_lift_lsmul R S S
  · rintro ⟨h, -⟩
    exact ⟨by simpa [lmul'_toLinearMap] using h⟩

theorem algebra_isEpi_iff_bijective_includeLeft :
    Algebra.IsEpi R S ↔ Function.Bijective includeLeft := by
  rw [algebra_isEpi_iff_bijective_lmul]
  constructor
  · intro h
    have hleft : Function.LeftInverse lmul' includeLeft := fun s ↦ by
      simp
    have hright : Function.RightInverse lmul' includeLeft := fun x ↦ by
      apply h.1
      simp
    exact ⟨hleft.injective, hright.surjective⟩
  · intro h
    refine ⟨?_, ?_⟩
    · intro x y hxy
      obtain ⟨x', rfl⟩ := h.2 x
      obtain ⟨y', rfl⟩ := h.2 y
      have hxy' : x' = y' := by
        simpa using hxy
      simp [hxy']
    · intro s
      exact ⟨includeLeft s, by simp⟩

-- Proof sketch: use `Algebra.isEpi_iff_forall_one_tmul_eq` to identify epimorphy with equality of
-- the two canonical tensor-factor maps; the multiplication map is inverse to `includeLeft` once
-- these maps agree, and conversely any inverse for one of the canonical maps forces the tensor
-- product to collapse to the diagonal.
/-- Lemma 10.107.1: for a commutative semiring map `R → S` (in particular for a commutative ring
map `R → S`), the following are equivalent: `R → S` is an epimorphism, the two canonical algebra
maps `S → S ⊗[R] S` are equal, the left canonical algebra map `S → S ⊗[R] S` is bijective, and
the multiplication map `S ⊗[R] S → S` is bijective. This uses the left tensor-factor map as the
canonical representative of the source-text clause that either of the two maps `S → S ⊗[R] S` is
an isomorphism. -/
theorem algebra_isEpi_tfae_includeLeft_eq_bijective_lmul :
    List.TFAE
      [ Algebra.IsEpi R S
      , includeLeft = includeRight
      , Function.Bijective includeLeft
      , Function.Bijective lmul'
      ] := by
  tfae_have 1 ↔ 2 := algebra_isEpi_iff_includeLeft_eq_includeRight
  tfae_have 1 ↔ 3 := algebra_isEpi_iff_bijective_includeLeft
  tfae_have 1 ↔ 4 := algebra_isEpi_iff_bijective_lmul
  tfae_finish

end
