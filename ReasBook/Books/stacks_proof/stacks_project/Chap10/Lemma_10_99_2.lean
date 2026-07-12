import Mathlib
import StacksProject_2024.Chap10.Lemma_10_99_1

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

open IsLocalRing
open scoped nonZeroDivisors

section

variable {R : Type u} {S : Type v}
variable [CommRing R] [CommRing S] [Algebra R S]
variable [IsLocalRing R] [IsLocalRing S] [IsLocalHom (algebraMap R S)]
variable [IsNoetherianRing S] [Module.Flat R S]

local notation "𝔪S" => Ideal.map (algebraMap R S) (maximalIdeal R)

-- Proof sketch: apply Lemma `10.99.1` to the `R`-linear endomorphism of `S` given by
-- multiplication by `f`. The hypothesis says exactly that the induced map on the fibre ring
-- `S / 𝔪S` is injective, so Lemma `10.99.1` gives flatness of the cokernel, which is `S / fS`,
-- and injectivity of multiplication by `f` on `S`, i.e. that `f` is regular in the canonical
-- mathlib sense and hence a nonzerodivisor in `S`.
/-- Lemma 10.99.2: if `R → S` is a flat local homomorphism of Noetherian local rings and the
image of `f` in the fibre ring `S / 𝔪S`, where `𝔪` is the maximal ideal of `R`, is a
nonzerodivisor, then `S / fS` is flat over `R` and `f` is a nonzerodivisor in `S`. -/
@[stacks 00MF]
theorem flat_quotient_and_nonZeroDivisor_of_fiber_nonZeroDivisor (f : S)
    (hbar : IsRegular (Ideal.Quotient.mk 𝔪S f)) :
    Module.Flat R (S ⧸ Ideal.span ({f} : Set S)) ∧ IsRegular f := by
  -- Work with the `R`-linear endomorphism given by multiplication by `f`.
  let u : S →ₗ[R] S := (LinearMap.mul R S) f
  have hf : Ideal.Quotient.mk 𝔪S f ∈ nonZeroDivisors (S ⧸ 𝔪S) := by
    exact isRegular_iff_mem_nonZeroDivisors.mp hbar
  -- The closed-fiber hypothesis is exactly injectivity of the quotient map of `u`.
  have hmod : Function.Injective (u.quotientMapByIdeal (maximalIdeal R)) := by
    intro x y hxy
    refine Quotient.inductionOn₂' x y ?_ hxy
    intro a b hab
    have hab' : (Submodule.Quotient.mk (f * a) : S ⧸ maximalIdeal R • (⊤ : Submodule R S)) =
        Submodule.Quotient.mk (f * b) := by
      simpa [LinearMap.quotientMapByIdeal] using hab
    have hab'' : f * a - f * b ∈ maximalIdeal R • (⊤ : Submodule R S) :=
      (Submodule.Quotient.eq _).1 hab'
    apply (Submodule.Quotient.eq _).2
    rw [Ideal.smul_top_eq_map] at hab'' ⊢
    change f * a - f * b ∈ 𝔪S at hab''
    change a - b ∈ 𝔪S
    have hmul : f * (a - b) ∈ 𝔪S := by
      simpa [mul_sub] using hab''
    have hfiber_zero : Ideal.Quotient.mk 𝔪S (a - b) = 0 := by
      rw [mem_nonZeroDivisors_iff_right] at hf
      have hquot_mul_zero :
          Ideal.Quotient.mk 𝔪S (a - b) * Ideal.Quotient.mk 𝔪S f = 0 := by
        rw [← map_mul, Ideal.Quotient.eq_zero_iff_mem]
        simpa [mul_comm] using hmul
      exact hf (Ideal.Quotient.mk 𝔪S (a - b)) hquot_mul_zero
    exact (Ideal.Quotient.eq_zero_iff_mem).1 hfiber_zero
  -- Lemma `10.99.1` turns the closed-fiber injectivity into flatness of the cokernel.
  have hrange : LinearMap.range u = (Ideal.span ({f} : Set S)).restrictScalars R := by
    simp [u]
  have hflatRange : Module.Flat R (S ⧸ LinearMap.range u) := by
    exact
      flat_quotient_of_mod_maximalIdeal_injective
        (R := R) (S := S) (M := S) (N := S) u hmod
  have hflatRestrict : Module.Flat R (S ⧸ (Ideal.span ({f} : Set S)).restrictScalars R) := by
    rw [hrange] at hflatRange
    exact hflatRange
  have e :
      (S ⧸ Ideal.span ({f} : Set S)) ≃ₗ[R] S ⧸ (Ideal.span ({f} : Set S)).restrictScalars R :=
    (Submodule.Quotient.restrictScalarsEquiv R (Ideal.span ({f} : Set S) : Ideal S)).symm
  have hflat : Module.Flat R (S ⧸ Ideal.span ({f} : Set S)) := by
    exact Module.Flat.of_linearEquiv e
  -- The same owner theorem also recovers injectivity of multiplication by `f`.
  have hinj : Function.Injective u := by
    exact injective_of_mod_maximalIdeal_injective (R := R) (S := S) (M := S) (N := S) u hmod
  have hregular : IsRegular f := by
    rw [isRegular_iff_mem_nonZeroDivisors, mem_nonZeroDivisors_iff_left]
    intro x hx
    have hmul_zero : u x = u 0 := by
      simpa [u] using hx
    simpa using hinj hmul_zero
  exact ⟨hflat, hregular⟩

end
