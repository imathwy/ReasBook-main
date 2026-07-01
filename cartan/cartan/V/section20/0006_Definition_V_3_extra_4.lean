import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open scoped Complex Topology

-- Semantic recall note: the dedicated `lean_leansearch` tool was unavailable in this runner, so
-- the Γ-function surface below was checked directly against mathlib's `Complex.Gamma`,
-- `Complex.Gamma_add_one`, `Complex.Gamma_nat_eq_factorial`,
-- `Complex.Gamma_mul_Gamma_one_sub`, `Complex.Gamma_one_half_eq`, and `Meromorphic.Gamma`.

namespace Complex

scoped notation "Γ" => Gamma

end Complex

/- Definition V.3-extra-4: the textbook `Γ`-function is the canonical complex Gamma function
`Complex.Gamma`. The recurrence relation, normalization `Γ(1) = 1`, factorial values
`Γ(n + 1) = n!`, Euler reflection formula, and the value `Γ(1 / 2) = √π` are available under the
checked mathlib names below. -/
#check Γ
#check Complex.Gamma_add_one
#check Complex.Gamma_one
#check Complex.Gamma_nat_eq_factorial
#check Complex.Gamma_mul_Gamma_one_sub
#check Complex.Gamma_one_half_eq
#check Meromorphic.Gamma

/-- Definition V.3-extra-4: every nonpositive integer is a simple pole of the complex Gamma
function. -/
theorem gamma_simple_pole_at_nonpositive_integer (n : ℕ) :
    meromorphicOrderAt Γ (-(n : ℂ)) = (-1 : WithTop ℤ) := by
  have hGamma : Meromorphic Γ := Meromorphic.Gamma
  induction n with
  | zero =>
      have hmul_meromorphic : MeromorphicAt (fun z : ℂ ↦ z * Γ z) 0 := by
        have hid : MeromorphicAt (fun z : ℂ ↦ z) 0 := analyticAt_id.meromorphicAt
        have hGamma0 : MeromorphicAt Γ 0 := hGamma.meromorphicAt
        exact hid.mul hGamma0
      have hmul_order :
          meromorphicOrderAt (fun z : ℂ ↦ z * Γ z) 0 = (0 : WithTop ℤ) := by
        rw [← tendsto_ne_zero_iff_meromorphicOrderAt_eq_zero hmul_meromorphic]
        refine ⟨1, one_ne_zero, ?_⟩
        simpa using Complex.tendsto_self_mul_Gamma_nhds_zero
      have hsum :
          (1 : WithTop ℤ) + meromorphicOrderAt Γ 0 = (0 : WithTop ℤ) := by
        calc
          (1 : WithTop ℤ) + meromorphicOrderAt Γ 0 =
              meromorphicOrderAt (fun z : ℂ ↦ z * Γ z) 0 := by
                have hGamma0 : MeromorphicAt Γ 0 := hGamma.meromorphicAt
                simpa using
                  (meromorphicOrderAt_mul analyticAt_id.meromorphicAt hGamma0).symm
          _ = 0 := hmul_order
      have hzero : meromorphicOrderAt Γ 0 = (-1 : WithTop ℤ) := by
        cases horder : meromorphicOrderAt Γ 0 with
        | top =>
            simp [horder] at hsum
        | coe m =>
            have hm : m = -1 := by
              have hsum' : (1 : WithTop ℤ) + (m : WithTop ℤ) = 0 := by
                simpa [horder] using hsum
              have hsum'' : ((m + 1 : ℤ) : WithTop ℤ) = 0 := by
                simpa [WithTop.coe_add, add_assoc, add_comm, add_left_comm] using hsum'
              have hsum''' : m + 1 = 0 := by
                exact_mod_cast hsum''
              linarith
            simp [hm]
      simpa using hzero
  | succ n ih =>
      let x : ℂ := -((n : ℂ) + 1)
      have hx_ne_zero : x ≠ 0 := by
        have hsucc : (n : ℂ) + 1 ≠ 0 := by
          exact_mod_cast Nat.succ_ne_zero n
        simpa [x] using neg_ne_zero.mpr hsucc
      have hshift :
          meromorphicOrderAt (fun z : ℂ ↦ Γ (z + 1)) x =
            meromorphicOrderAt Γ (-(n : ℂ)) := by
        have hanalytic : AnalyticAt ℂ (fun z : ℂ ↦ z + 1) x := by
          fun_prop
        have hderiv : deriv (fun z : ℂ ↦ z + 1) x ≠ 0 := by
          simp
        simpa [Function.comp, x] using
          meromorphicOrderAt_comp_of_deriv_ne_zero hanalytic hderiv
      have hrecurrence :
          (fun z : ℂ ↦ Γ (z + 1)) =ᶠ[𝓝[≠] x] fun z ↦ z * Γ z := by
        have hne : ∀ᶠ z in 𝓝[≠] x, z ≠ 0 :=
          (eventually_ne_nhds hx_ne_zero).filter_mono nhdsWithin_le_nhds
        filter_upwards [hne] with z hz
        exact Complex.Gamma_add_one z hz
      have hmul :
          meromorphicOrderAt (fun z : ℂ ↦ z * Γ z) x =
            meromorphicOrderAt Γ x := by
        have hanalytic : AnalyticAt ℂ (fun z : ℂ ↦ z) x := analyticAt_id
        simpa using meromorphicOrderAt_mul_of_ne_zero hanalytic hx_ne_zero
      calc
        meromorphicOrderAt Γ (-(n.succ : ℂ)) =
            meromorphicOrderAt Γ x := by
              simp [x, Nat.cast_add]
        _ = meromorphicOrderAt (fun z : ℂ ↦ z * Γ z) x := hmul.symm
        _ = meromorphicOrderAt (fun z : ℂ ↦ Γ (z + 1)) x := by
              rw [meromorphicOrderAt_congr hrecurrence]
        _ = meromorphicOrderAt Γ (-(n : ℂ)) := hshift
        _ = (-1 : WithTop ℤ) := ih
