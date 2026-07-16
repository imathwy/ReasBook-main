import StacksProject_2024.stacks_project.Chap10.Lemma_10_63_14

-- Declarations for this item will be appended below by the statement pipeline.

attribute [local instance] Algebra.TensorProduct.rightAlgebra

open Ideal.Quotient (eq_zero_iff_mem)
open scoped TensorProduct

universe u v w

section

variable {R : Type u} {S : Type v} {N : Type w}
variable [CommRing R] [CommRing S] [Algebra R S]
variable (p : Ideal R) [p.IsPrime]
variable [AddCommGroup N] [Module S N]

local notation "Sbar" => S ⧸ p.map (algebraMap R S)
local notation "Nfiber" => (p.Fiber S) ⊗[S] N

-- Elements of `pS` vanish in `κ(p) ⊗[R] S`.
private lemma algebraMap_fiber_eq_zero_of_mem_map {x : S} (hx : x ∈ p.map (algebraMap R S)) :
    algebraMap S (p.Fiber S) x = 0 := by
  let φ : (R ⧸ p) ⊗[R] S →+* p.Fiber S :=
    (Algebra.TensorProduct.map (IsScalarTower.toAlgHom R (R ⧸ p) p.ResidueField)
      (AlgHom.id R S)).toRingHom
  have hquot :
      (Ideal.Quotient.mk (p.map (algebraMap R S)) x : S ⧸ p.map (algebraMap R S)) = 0 :=
    eq_zero_iff_mem.mpr hx
  have htmul : (1 : R ⧸ p) ⊗ₜ[R] x = 0 := by
    let e := Algebra.TensorProduct.quotIdealMapEquivQuotTensor S p
    have : e (Ideal.Quotient.mk (p.map (algebraMap R S)) x) = (1 : R ⧸ p) ⊗ₜ[R] x := rfl
    rw [← this, hquot]
    simp [e]
  have hφ : φ ((1 : R ⧸ p) ⊗ₜ[R] x) = 0 := by
    rw [htmul, map_zero]
  simpa [φ] using hφ

private noncomputable instance :
    Algebra Sbar (p.Fiber S) :=
  (Ideal.Quotient.liftₐ (p.map (algebraMap R S)) (Algebra.ofId S (p.Fiber S))
    fun _ hx ↦ algebraMap_fiber_eq_zero_of_mem_map p hx).toRingHom.toAlgebra

/- Domain triage:
* `source-facing`: the two equalities in Remark 10.65.6 for associated primes of the fiber module.
* `core/canonical`: the owner theorem
  `associatedPrimesOfModule_quotient_image_comap_eq` for contraction along a quotient map.
* `bridge/view`: the local `Sbar`-algebra structure on `p.Fiber S`, used only to state the
  source-facing fiber comparison for the canonical tensor model `Nfiber`.
-/

/- Remark 10.65.6, first equality: for the canonical fiber module modeling
`N ⊗_R κ(p)`, the comparison between associated primes over `S` and over `S ⧸ pS` is exactly the
specialization of the owner theorem
`associatedPrimesOfModule_quotient_image_comap_eq` to the ideal `pS = p.map (algebraMap R S)` and
the `S`-module `Nfiber`. -/
#check
  (associatedPrimesOfModule_quotient_image_comap_eq (p.map (algebraMap R S)) :
    Ideal.comap (Ideal.Quotient.mk (p.map (algebraMap R S))) ''
        associatedPrimesOfModule Sbar Nfiber =
      associatedPrimesOfModule S Nfiber)

/-- Remark 10.65.6, second equality: for the same fiber module, the textbook associated primes
over `S ⧸ pS` agree with those over the fiber ring `κ(p) ⊗[R] S` after transporting them back to
ideals of `S`. -/
theorem associatedPrimesOfModule_fiberTensor_over_quotient_eq_over_fiber :
    Ideal.comap (Ideal.Quotient.mk (p.map (algebraMap R S))) ''
        associatedPrimesOfModule Sbar Nfiber =
      Ideal.comap (algebraMap S (p.Fiber S)) ''
        associatedPrimesOfModule (p.Fiber S) Nfiber := sorry

end
