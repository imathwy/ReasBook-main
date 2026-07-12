import Mathlib

open Module
open scoped BigOperators

noncomputable section

variable {k L : Type*} [Field k] [Field L] [Algebra k L] [FiniteDimensional k L] [IsGalois k L]
variable {ι : Type*} [Fintype ι] [DecidableEq ι] (b : Basis ι k L)

-- card of Gal = card ι
example : Fintype.card (L ≃ₐ[k] L) = Fintype.card ι := by
  rw [← Nat.card_eq_fintype_card (α := L ≃ₐ[k] L), IsGalois.card_aut_eq_finrank,
    Module.finrank_eq_card_basis b]

-- Orthogonality: ∑_i b_i * τ(b'_i) = if τ = 1 then 1 else 0
example (τ : L ≃ₐ[k] L) [DecidableEq (L ≃ₐ[k] L)] :
    ∑ i, b i * τ (b.traceDual i) = if τ = 1 then 1 else 0 := by
  classical
  let U : Matrix (L ≃ₐ[k] L) ι L := fun σ i => σ (b i)
  let V : Matrix ι (L ≃ₐ[k] L) L := fun i σ => σ (b.traceDual i)
  -- V * U = 1
  have hVU : V * U = 1 := by
    ext i j
    simp only [Matrix.mul_apply, V, U]
    rw [show (∑ σ : L ≃ₐ[k] L, σ (b.traceDual i) * σ (b j))
        = ∑ σ : L ≃ₐ[k] L, σ (b.traceDual i * b j) from
        Finset.sum_congr rfl (fun σ _ => (map_mul σ _ _).symm)]
    rw [← trace_eq_sum_automorphisms, b.trace_traceDual_mul i j, Matrix.one_apply,
      apply_ite (algebraMap k L), map_one, map_zero]
    simp only [eq_comm]
  -- card equality
  have hcard : Fintype.card (L ≃ₐ[k] L) = Fintype.card ι := by
    rw [← Nat.card_eq_fintype_card (α := L ≃ₐ[k] L), IsGalois.card_aut_eq_finrank,
      Module.finrank_eq_card_basis b]
  have hUV : U * V = 1 :=
    (Matrix.mul_eq_one_comm_of_card_eq (L ≃ₐ[k] L) ι L hcard).mpr hVU
  have hflip := congrFun (congrFun hUV 1) τ
  simp only [Matrix.mul_apply, U, V, Matrix.one_apply, AlgEquiv.one_apply] at hflip
  simp only [eq_comm (a := (1 : L ≃ₐ[k] L)) (b := τ)] at hflip
  exact hflip
