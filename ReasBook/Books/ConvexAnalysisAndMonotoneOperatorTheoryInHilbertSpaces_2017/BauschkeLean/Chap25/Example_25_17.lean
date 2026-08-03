import BauschkeLean.Chap17.Proposition_17_36
import BauschkeLean.Chap20.Example_20_16
import BauschkeLean.Chap20.Example_20_54
import BauschkeLean.Chap25.Definition_25_10

open scoped ERealFunction InnerProductSpace SetValuedOperator

universe u v

namespace ContinuousLinearMap

section RealHilbert

variable {H : Type u} {K : Type v}
variable [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
variable [NormedAddCommGroup K] [InnerProductSpace ℝ K] [CompleteSpace K]

-- Semantic recall: this item uses the Chapter 25 owner
-- `SetValuedOperator.IsThreeStarMonotone` through the singleton-valued bridge
-- `ContinuousLinearMap.toSetValuedOperator`, together with the Chapter 20 singleton Fitzpatrick
-- formula and the Chapter 17 quadratic-potential conjugate owner on range points.

/-- Example 25.17: if `L : H →L[ℝ] K` is a bounded linear operator between real Hilbert spaces,
then `L.comp L.adjoint` is `3*` monotone. -/
theorem self_comp_adjoint_isThreeStarMonotone (L : H →L[ℝ] K) :
    ((L.comp L.adjoint).toSetValuedOperator).IsThreeStarMonotone := by
  let A : K →L[ℝ] K := L.comp L.adjoint
  have hA_self : IsSelfAdjoint A := (isPositive_self_comp_adjoint L).isSelfAdjoint
  have hA_mono : A.toLinearMap.IsMonotone := by
    simpa [A] using (isPositive_self_comp_adjoint L).toLinearMap.isMonotone
  have hconj_apply :
      ∀ y : K, ((q[A]).toEReal.asEReal∗) (A y) = ((q[A] y : ℝ) : EReal) := by
    intro y
    rw [ERealFunction.conjugate_apply]
    apply le_antisymm
    · refine iSup_le fun x ↦ ?_
      have hdefect :
          ⟪x, A y⟫_ℝ - q[A] x = q[A] y - q[A] (x - y) :=
        pairing_sub_quadraticPotential_eq_quadraticPotential_sub_of_eq_apply A hA_self rfl x
      have hnonneg : 0 ≤ q[A] (x - y) :=
        quadraticPotential_nonneg_of_isMonotone A hA_mono (x - y)
      have hle : ⟪x, A y⟫_ℝ - q[A] x ≤ q[A] y := by
        rw [hdefect]
        linarith
      calc
        (((⟪x, A y⟫_ℝ : ℝ) : EReal) - (q[A]).toEReal.asEReal x) =
            ((⟪x, A y⟫_ℝ - q[A] x : ℝ) : EReal) := by
              simp [Function.asEReal_apply, Function.toEReal_apply]
        _ ≤ ((q[A] y : ℝ) : EReal) := by
              exact_mod_cast hle
    · have hy :
          ⟪y, A y⟫_ℝ - q[A] y = q[A] y := by
        simpa using
          (show ⟪y, A y⟫_ℝ - q[A] y = q[A] y - q[A] (y - y) from
            pairing_sub_quadraticPotential_eq_quadraticPotential_sub_of_eq_apply A hA_self rfl y)
      calc
        ((q[A] y : ℝ) : EReal) = ((⟪y, A y⟫_ℝ - q[A] y : ℝ) : EReal) := by
          exact_mod_cast hy.symm
        _ = (((⟪y, A y⟫_ℝ : ℝ) : EReal) - (q[A]).toEReal.asEReal y) := by
          simp [Function.asEReal_apply, Function.toEReal_apply]
        _ ≤ ⨆ x : K, (((⟪x, A y⟫_ℝ : ℝ) : EReal) - (q[A]).toEReal.asEReal x) := by
          exact le_iSup (fun x : K ↦ (((⟪x, A y⟫_ℝ : ℝ) : EReal) - (q[A]).toEReal.asEReal x)) y
  rw [SetValuedOperator.isThreeStarMonotone_iff]
  rintro ⟨x, u⟩ ⟨_, hu_range⟩
  rw [ERealFunction.mem_dom_iff_ne_top]
  rcases (SetValuedOperator.mem_range_iff A.toSetValuedOperator u).1 hu_range with ⟨z, hz⟩
  have huz : u = A z := by
    simpa using hz
  have hshift :
      ((1 / 2 : ℝ) • u) + ((1 / 2 : ℝ) • A x) = A (((1 / 2 : ℝ) • z) + ((1 / 2 : ℝ) • x)) := by
    rw [huz, map_add, map_smul, map_smul]
  have hconj_ne_top :
      ((q[A]).toEReal.asEReal∗) (((1 / 2 : ℝ) • u) + ((1 / 2 : ℝ) • A x)) ≠ ⊤ := by
    rw [hshift, hconj_apply]
    exact EReal.coe_ne_top _
  have hfitz :
      F[A.toSetValuedOperator] (x, u) =
        ((2 : ℝ) : EReal) * ((q[A]).toEReal.asEReal∗)
          (((1 / 2 : ℝ) • u) + ((1 / 2 : ℝ) • A x)) := by
    simpa [hA_self.adjoint_eq] using
      fitzpatrickFunction_eq_two_mul_conjugate_quadraticPotential A x u
  rw [hfitz]
  rw [EReal.mul_ne_top]
  exact ⟨Or.inl (by simp), Or.inl (by norm_num), Or.inl (by simp), Or.inr hconj_ne_top⟩

end RealHilbert

end ContinuousLinearMap
