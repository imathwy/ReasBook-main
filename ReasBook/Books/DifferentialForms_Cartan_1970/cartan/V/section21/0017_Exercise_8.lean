import Mathlib
import DifferentialForms_Cartan_1970.cartan.V.section20.«0006_Definition_V_3_extra_4»

-- Declarations for this item will be appended below by the statement pipeline.

open Filter
open scoped Complex Nat Topology

-- Domain sampling: this exercise lies in the complex Gamma-function domain.
-- Sampled owner-layer declarations:
-- * `Γ` from `0006_Definition_V_3_extra_4`
-- * `meromorphicTrailingCoeffAt`
-- * `Complex.Gamma_add_one`
-- * `Complex.tendsto_self_mul_Gamma_nhds_zero`
-- * `MeromorphicAt.tendsto_nhds_meromorphicTrailingCoeffAt`
-- Owner abstraction: the residue owner in this domain is `meromorphicTrailingCoeffAt` on `Γ`.
-- Primitive data: the Gamma function together with its recurrence and simple-pole order data.
-- Derived API: the punctured-limit computation of the residue at the poles `z = -n`.
-- Layer triage: the main theorem is `source-facing`, and the punctured-limit theorem is its
-- `bridge/view` companion on the same canonical `Γ` surface.

-- `lean_leansearch` was unavailable in this environment; the canonical Gamma-function surface for
-- this item was checked locally against `Complex.tendsto_self_mul_Gamma_nhds_zero`,
-- `Complex.Gamma_add_one`, `meromorphicTrailingCoeffAt`,
-- `MeromorphicAt.tendsto_nhds_meromorphicTrailingCoeffAt`, and `Meromorphic.Gamma`.

/-- Bridge/view form of Exercise 8: `(z + n) * Γ(z)` tends on the punctured neighborhood of `-n`
to the residue value `(-1)^n / n!`. -/
theorem tendsto_gamma_residue_at_neg_nat (n : ℕ) :
    Tendsto
      (fun z : ℂ ↦ (z + (n : ℂ)) * Γ z)
      (𝓝[≠] (-(n : ℂ)))
      (𝓝 (((-1 : ℂ) ^ n) / ((n)! : ℂ))) := by
  induction n with
  | zero =>
      convert Complex.tendsto_self_mul_Gamma_nhds_zero using 1 <;> simp
  | succ n ih =>
      let a : ℂ := -((n.succ : ℂ))
      have ha : a ≠ 0 := by
        exact neg_ne_zero.mpr <| by exact_mod_cast Nat.succ_ne_zero n
      have hshift :
          Tendsto (fun z : ℂ ↦ z + 1) (𝓝[≠] a) (𝓝[≠] (-(n : ℂ))) := by
        rw [Filter.Tendsto]
        convert ((Homeomorph.addRight (1 : ℂ)).map_punctured_nhds_eq a).le using 1;
          simp [a, Nat.cast_add, add_assoc]
      have hnum :
          Tendsto
            (fun z : ℂ ↦ ((z + 1) + (n : ℂ)) * Γ (z + 1))
            (𝓝[≠] a)
            (𝓝 (((-1 : ℂ) ^ n) / ((n)! : ℂ))) :=
        ih.comp hshift
      have hinv :
          Tendsto (fun z : ℂ ↦ z⁻¹) (𝓝[≠] a) (𝓝 (a⁻¹)) := by
        exact (continuousAt_inv₀ ha).tendsto.comp
          ((continuousAt_id.tendsto : Tendsto (fun z : ℂ ↦ z) (𝓝 a) (𝓝 a)).mono_left
            nhdsWithin_le_nhds)
      have hmul :
          Tendsto
            (fun z : ℂ ↦ (((z + 1) + (n : ℂ)) * Γ (z + 1)) * z⁻¹)
            (𝓝[≠] a)
            (𝓝 ((((-1 : ℂ) ^ n) / ((n)! : ℂ)) * a⁻¹)) :=
        hnum.mul hinv
      have hEq :
          (fun z : ℂ ↦ (z + (n.succ : ℂ)) * Γ z) =ᶠ[𝓝[≠] a]
            fun z ↦ (((z + 1) + (n : ℂ)) * Γ (z + 1)) * z⁻¹ := by
        have hz :
            ∀ᶠ z in 𝓝[≠] a, z ≠ 0 :=
          (eventually_ne_nhds ha).filter_mono nhdsWithin_le_nhds
        filter_upwards [hz] with z hz
        rw [Complex.Gamma_add_one z hz]
        calc
          (z + (n.succ : ℂ)) * Γ z = (((z + 1) + (n : ℂ)) * Γ z) * (z * z⁻¹) := by
                simp [Nat.cast_add, add_comm, add_left_comm, hz]
          _ = (((z + 1) + (n : ℂ)) * (z * Γ z)) * z⁻¹ := by ring
      have hlimit :
          (((-1 : ℂ) ^ n) / ((n)! : ℂ)) * a⁻¹ =
            (((-1 : ℂ) ^ n.succ) / ((n.succ)! : ℂ)) := by
        dsimp [a]
        rw [Nat.factorial_succ, Nat.cast_mul, div_eq_mul_inv, pow_succ, inv_neg]
        ring_nf
      have hres :
          Tendsto
            (fun z : ℂ ↦ (z + (n.succ : ℂ)) * Γ z)
            (𝓝[≠] a)
            (𝓝 (((-1 : ℂ) ^ n.succ) / ((n.succ)! : ℂ))) := by
        exact hlimit ▸ hmul.congr' hEq.symm
      simpa [a] using hres

/-- Exercise 8: the residue of the complex Gamma function at the pole `z = -n` is
`(-1)^n / n!`. -/
theorem exercise_8_gamma_residue_at_neg_nat (n : ℕ) :
    meromorphicTrailingCoeffAt Γ (-(n : ℂ)) = ((-1 : ℂ) ^ n) / ((n)! : ℂ) := by
  have hGamma : MeromorphicAt Γ (-(n : ℂ)) := Meromorphic.Gamma.meromorphicAt
  have hcoeff_tendsto := hGamma.tendsto_nhds_meromorphicTrailingCoeffAt
  have hcoeff_tendsto0 :
      Tendsto
        (((fun z : ℂ ↦ z + (n : ℂ)) ^ (WithTop.untop₀ (1 : WithTop ℤ))) * Γ)
        (𝓝[≠] (-(n : ℂ)))
        (𝓝 (meromorphicTrailingCoeffAt Γ (-(n : ℂ)))) := by
    simpa [gamma_simple_pole_at_nonpositive_integer, sub_eq_add_neg, add_assoc, add_left_comm,
      add_comm] using hcoeff_tendsto
  have hcoeff_tendsto' :
      Tendsto
        (fun z : ℂ ↦ (z + (n : ℂ)) * Γ z)
        (𝓝[≠] (-(n : ℂ)))
        (𝓝 (meromorphicTrailingCoeffAt Γ (-(n : ℂ)))) := by
    have hone : WithTop.untop₀ (1 : WithTop ℤ) = (1 : ℤ) := by
      rfl
    have hfun :
        (((fun z : ℂ ↦ z + (n : ℂ)) ^ (WithTop.untop₀ (1 : WithTop ℤ))) * Γ) =
          (fun z : ℂ ↦ (z + (n : ℂ)) * Γ z) := by
      ext z
      rw [Pi.mul_apply, Pi.pow_apply, hone, zpow_one]
    exact hfun ▸ hcoeff_tendsto0
  exact tendsto_nhds_unique hcoeff_tendsto' (tendsto_gamma_residue_at_neg_nat n)
