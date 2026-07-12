import Mathlib

open CategoryTheory
open CategoryTheory.Abelian
open CategoryTheory.Abelian.Ext

universe u

variable {R M N : Type u} [CommRing R]
variable [AddCommGroup M] [Module R M]
variable [AddCommGroup N] [Module R N]

local notation "M_" => ModuleCat.of R M
local notation "N_" => ModuleCat.of R N

/- Domain triage:
* primary domain: linear `Ext` groups in `ModuleCat R`;
* sampled owner declarations: `smul_eq_comp_mk₀`, `mk₀_smul`, `smul_comp`, and
  `mk₀_eq_zero_iff`;
* core/canonical owner abstraction: the `R`-module structure on `Ext` in the linear abelian
  category `ModuleCat R`, with source and target scalar actions both expressed through `mk₀`;
* source-facing layer: the annihilator statement for `Ext^i_R(M, N)`;
* primitive data: the scalar `x`, the two `R`-modules `M` and `N`, the degree `i`, and the class
  `e : Ext^i_R(M, N)`;
* derived API: target-side scalar action via `smul_eq_comp_mk₀`, source-side scalar action via
  `mk₀_smul`, `smul_comp`, and `mk₀_id_comp`, and zero detection via `mk₀_eq_zero_iff`.

This item is therefore `source-facing`: it adds a textbook annihilator statement about the
canonical owner object `Ext`, so the refinement is to consume the owner linearity API directly
rather than routing through a parallel resolution-level public wrapper. -/

/-- Lemma 10.71.8: if `x : R` annihilates either `N` or `M`, then it annihilates the Ext module
`Ext^i_R(M, N)` for every `i`. -/
-- Proof sketch: if `x` annihilates `N`, then `x • 𝟙_N = 0`, and `smul_eq_comp_mk₀` identifies
-- scalar multiplication by `x` on `Ext` with postcomposition by `mk₀ (x • 𝟙_N) = 0`. If `x`
-- annihilates `M`, then `mk₀_smul`, `smul_comp`, and `mk₀_id_comp` identify scalar
-- multiplication by `x` on `Ext` with precomposition by `mk₀ (x • 𝟙_M) = 0`.
@[stacks 00LV]
theorem smul_ext_eq_zero_of_annihilates_target_or_source {x : R}
    (hx : (∀ n : N, x • n = 0) ∨ ∀ m : M, x • m = 0)
    (i : ℕ) (e : Ext M_ N_ i) :
    x • e = 0 := by
  rcases hx with hN | hM
  · have hmk₀ : mk₀ (x • 𝟙 N_) = 0 := by
      rw [mk₀_eq_zero_iff]
      ext n
      simpa using hN n
    rw [smul_eq_comp_mk₀]
    calc
      e.comp (mk₀ (x • 𝟙 N_)) (add_zero i) = e.comp 0 (add_zero i) := by
        simp [hmk₀]
      _ = 0 := by rw [comp_zero]
  · have hmk₀ : mk₀ (x • 𝟙 M_) = 0 := by
      rw [mk₀_eq_zero_iff]
      ext m
      simpa using hM m
    calc
      x • e = x • ((mk₀ (𝟙 M_)).comp e (zero_add i)) := by
        rw [mk₀_id_comp]
      _ = (x • mk₀ (𝟙 M_)).comp e (zero_add i) := by
        rw [smul_comp]
      _ = (mk₀ (x • 𝟙 M_)).comp e (zero_add i) := by
        simpa using congrArg (fun α : Ext M_ M_ 0 ↦ α.comp e (zero_add i))
          (mk₀_smul x (𝟙 M_)).symm
      _ = 0 := by
        rw [hmk₀, zero_comp]
