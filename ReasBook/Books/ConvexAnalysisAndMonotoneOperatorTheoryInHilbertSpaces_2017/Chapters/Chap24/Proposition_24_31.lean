import BauschkeLean.Chap04.FirmlyNonexpansiveOn
import BauschkeLean.Chap16.Proposition_16_44
import BauschkeLean.Chap20.Theorem_20_25
import BauschkeLean.Chap22.Corollary_22_23
import BauschkeLean.Chap23.Proposition_23_8

-- Declarations for this item will be appended below by the statement pipeline.

open SetValuedOperator
open scoped Pointwise SetValuedOperator

namespace ERealFunction

-- Semantic recall note: `lean_leansearch` returned only unrelated `Gamma`-function results, so
-- this item follows the verified local Chapter 12/22/23 surface `Prox[f, hf]`, `Γ₀(ℝ)`, and the
-- real-line bridge between firm nonexpansiveness and monotone `1`-Lipschitz self-maps.

/-- On `ℝ`, firm nonexpansiveness is equivalent to being both nonexpansive and increasing. The
canonical Lean surface uses `LipschitzWith 1` for nonexpansiveness and `Monotone` for increasing
functions. -/
theorem firmlyNonexpansive_iff_lipschitzWith_one_and_monotone_real
    (ρ : ℝ → ℝ) :
    FirmlyNonexpansive ρ ↔ LipschitzWith 1 ρ ∧ Monotone ρ := by
  constructor
  · intro hρ
    have hineq :
        ∀ x y : ℝ, (ρ x - ρ y) ^ (2 : ℕ) ≤ (ρ x - ρ y) * (x - y) := by
      intro x y
      have hxy := (firmlyNonexpansive_iff_norm_sq_le_inner.mp hρ) x y
      rw [show inner ℝ (ρ x - ρ y) (x - y) = (ρ x - ρ y) * (x - y) by
        simpa using RCLike.inner_apply' (ρ x - ρ y) (x - y)] at hxy
      simpa [pow_two] using hxy
    have hmono : Monotone ρ := by
      intro x y hxy
      by_cases hρxy : ρ x ≤ ρ y
      · exact hρxy
      · have hpos : 0 < ρ x - ρ y := sub_pos.mpr (lt_of_not_ge hρxy)
        have hxy' : x - y ≤ 0 := sub_nonpos.mpr hxy
        have hxy'' := hineq x y
        nlinarith
    have hdist : ∀ x y : ℝ, dist (ρ x) (ρ y) ≤ dist x y := by
      intro x y
      rcases le_total x y with hxy | hyx
      · have hρxy : ρ x ≤ ρ y := hmono hxy
        have hsub : ρ y - ρ x ≤ y - x := by
          have hxy' := hineq y x
          nlinarith [sub_nonneg.mpr hρxy, sub_nonneg.mpr hxy]
        have hdist' : |ρ y - ρ x| ≤ |y - x| := by
          simpa [abs_of_nonneg (sub_nonneg.mpr hρxy),
            abs_of_nonneg (sub_nonneg.mpr hxy)] using hsub
        simpa [Real.dist_eq, abs_sub_comm] using hdist'
      · have hρyx : ρ y ≤ ρ x := hmono hyx
        have hsub : ρ x - ρ y ≤ x - y := by
          have hxy' := hineq x y
          nlinarith [sub_nonneg.mpr hρyx, sub_nonneg.mpr hyx]
        have hdist' : |ρ x - ρ y| ≤ |x - y| := by
          simpa [abs_of_nonneg (sub_nonneg.mpr hρyx),
            abs_of_nonneg (sub_nonneg.mpr hyx)] using hsub
        simpa [Real.dist_eq] using hdist'
    exact ⟨LipschitzWith.mk_one hdist, hmono⟩
  · rintro ⟨hLip, hmono⟩
    rw [firmlyNonexpansive_iff_norm_sq_le_inner]
    intro x y
    rcases le_total x y with hxy | hyx
    · have hρxy : ρ x ≤ ρ y := hmono hxy
      have hdist : |ρ y - ρ x| ≤ |y - x| := by
        simpa [Real.dist_eq, abs_sub_comm] using hLip.dist_le_mul x y
      have hsub : ρ y - ρ x ≤ y - x := by
        simpa [abs_of_nonneg (sub_nonneg.mpr hρxy),
          abs_of_nonneg (sub_nonneg.mpr hxy)] using hdist
      have hfirm : (ρ x - ρ y) ^ (2 : ℕ) ≤ (ρ x - ρ y) * (x - y) := by
        nlinarith [hsub, sub_nonneg.mpr hρxy, sub_nonneg.mpr hxy]
      rw [show inner ℝ (ρ x - ρ y) (x - y) = (ρ x - ρ y) * (x - y) by
        simpa using RCLike.inner_apply' (ρ x - ρ y) (x - y)]
      simpa [pow_two] using hfirm
    · have hρyx : ρ y ≤ ρ x := hmono hyx
      have hdist : |ρ x - ρ y| ≤ |x - y| := by
        simpa [Real.dist_eq] using hLip.dist_le_mul x y
      have hsub : ρ x - ρ y ≤ x - y := by
        simpa [abs_of_nonneg (sub_nonneg.mpr hρyx),
          abs_of_nonneg (sub_nonneg.mpr hyx)] using hdist
      have hfirm : (ρ x - ρ y) ^ (2 : ℕ) ≤ (ρ x - ρ y) * (x - y) := by
        nlinarith [hsub, sub_nonneg.mpr hρyx, sub_nonneg.mpr hyx]
      rw [show inner ℝ (ρ x - ρ y) (x - y) = (ρ x - ρ y) * (x - y) by
        simpa using RCLike.inner_apply' (ρ x - ρ y) (x - y)]
      simpa [pow_two] using hfirm

/-- Helper for Proposition 24.31: on `ℝ`, a self-map is firmly nonexpansive exactly when it is
the resolvent `J[A]` of some maximally monotone operator `A : SetValuedOperator ℝ ℝ`. -/
theorem firmlyNonexpansive_iff_exists_maximal_isMonotone_resolvent_real
    (T : ℝ → ℝ) :
    FirmlyNonexpansive T ↔
      ∃ A : SetValuedOperator ℝ ℝ, Maximal IsMonotone A ∧ J[A] = T.toSetValuedOperator := by
  constructor
  · intro hT
    refine ⟨(ofFunction (Set.univ : Set ℝ) (fun x : Set.univ ↦ T x)).inverse -
      id.toSetValuedOperator, ?_, ?_⟩
    · simpa [FirmlyNonexpansive, Function.toSetValuedOperator] using
        (firmlyNonexpansiveOn_and_univ_iff_maximal_sub_id_inverse_ofFunction
          (Set.univ : Set ℝ) Set.univ_nonempty (fun x : Set.univ ↦ T x)).mp ⟨hT, rfl⟩
    · simpa [Function.toSetValuedOperator] using
        (resolvent_sub_id_inverse_ofFunction_eq_ofFunction
          (Set.univ : Set ℝ) Set.univ_nonempty (fun x : Set.univ ↦ T x))
  · rintro ⟨A, hA, hJ⟩
    have hmono : A.IsMonotone := SetValuedOperator.Maximal.isMonotone hA
    rw [firmlyNonexpansive_iff_norm_sq_le_inner]
    intro x y
    have hxJ : T x ∈ J[A] x := by
      simp [hJ, Function.toSetValuedOperator_apply]
    have hyJ : T y ∈ J[A] y := by
      simp [hJ, Function.toSetValuedOperator_apply]
    have hxA : x - T x ∈ A (T x) := by
      rw [resolvent_def, SetValuedOperator.mem_inverse_iff] at hxJ
      rw [Pi.add_apply, Function.toSetValuedOperator_apply, Set.mem_add] at hxJ
      rcases hxJ with ⟨z, hz, u, hu, hzu⟩
      rw [Set.mem_singleton_iff] at hz
      subst z
      have hzu' : T x + u = x := by
        simpa using hzu
      have hu_eq : u = x - T x := by
        linarith
      simpa [hu_eq] using hu
    have hyA : y - T y ∈ A (T y) := by
      rw [resolvent_def, SetValuedOperator.mem_inverse_iff] at hyJ
      rw [Pi.add_apply, Function.toSetValuedOperator_apply, Set.mem_add] at hyJ
      rcases hyJ with ⟨z, hz, v, hv, hzv⟩
      rw [Set.mem_singleton_iff] at hz
      subst z
      have hzv' : T y + v = y := by
        simpa using hzv
      have hv_eq : v = y - T y := by
        linarith
      simpa [hv_eq] using hv
    have hmonoxy :
        0 ≤ inner ℝ (T x - T y) ((x - T x) - (y - T y)) := by
      exact (SetValuedOperator.isMonotone_iff A).1 hmono hxA hyA
    rw [show inner ℝ (T x - T y) ((x - T x) - (y - T y)) =
        (T x - T y) * ((x - T x) - (y - T y)) by
      simpa using RCLike.inner_apply' (T x - T y) ((x - T x) - (y - T y))] at hmonoxy
    have hpow :
        (T x - T y) ^ (2 : ℕ) ≤ (T x - T y) * (x - y) := by
      nlinarith
    rw [show inner ℝ (T x - T y) (x - y) = (T x - T y) * (x - y) by
      simpa using RCLike.inner_apply' (T x - T y) (x - y)]
    simpa [pow_two] using hpow

/-- Proposition 24.31: a map `ρ : ℝ → ℝ` is the proximity operator of some `f ∈ Γ₀(ℝ)` if and
only if `ρ` is nonexpansive and increasing. On the canonical Lean surface, this is expressed as
`LipschitzWith 1 ρ ∧ Monotone ρ`. -/
theorem exists_eq_proximityOperator_iff_lipschitzWith_one_and_monotone_real
    (ρ : ℝ → ℝ) :
    (∃ (f : ℝ → Set.Ioi (⊥ : EReal)) (hf : f ∈ Γ₀(ℝ)), ρ = Prox[f, hf]) ↔
      LipschitzWith 1 ρ ∧ Monotone ρ := by
  rw [← firmlyNonexpansive_iff_lipschitzWith_one_and_monotone_real]
  constructor
  · rintro ⟨f, hf, rfl⟩
    refine (firmlyNonexpansive_iff_exists_maximal_isMonotone_resolvent_real (Prox[f, hf])).2 ?_
    refine ⟨∂ f, subdifferential_isMaximallyMonotone_of_mem_gammaZero hf, ?_⟩
    simpa [resolvent_def] using
      (singleton_proximityOperator_eq_inverse_add_subdifferential hf).symm
  · intro hρ
    rcases (firmlyNonexpansive_iff_exists_maximal_isMonotone_resolvent_real ρ).mp hρ with
      ⟨A, hA, hJ⟩
    rcases exists_mem_gammaZero_eq_subdifferential_of_isMaximalMonotone A hA with ⟨f, hf, hAeq⟩
    refine ⟨f, hf, ?_⟩
    have hprox : J[(∂ f : SetValuedOperator ℝ ℝ)] = (Prox[f, hf]).toSetValuedOperator := by
      simpa [resolvent_def] using
        (singleton_proximityOperator_eq_inverse_add_subdifferential hf).symm
    have hρset : ρ.toSetValuedOperator = (Prox[f, hf]).toSetValuedOperator := by
      calc
        ρ.toSetValuedOperator = J[A] := hJ.symm
        _ = J[(∂ f : SetValuedOperator ℝ ℝ)] := by rw [hAeq]
        _ = (Prox[f, hf]).toSetValuedOperator := hprox
    ext x
    apply Set.singleton_injective
    simpa using congrArg (fun T : SetValuedOperator ℝ ℝ ↦ T x) hρset

end ERealFunction
