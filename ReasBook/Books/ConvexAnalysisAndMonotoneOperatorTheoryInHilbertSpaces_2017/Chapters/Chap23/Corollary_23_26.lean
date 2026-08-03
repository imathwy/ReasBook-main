import BauschkeLean.Chap23.Proposition_23_25

open scoped InnerProductSpace Pointwise SetValuedOperator
open ERealFunction

universe u

namespace SetValuedOperator

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

private theorem isUnit_comp_adjoint_homothety {ρ : ℝ} (hρ : ρ ≠ 0) :
    IsUnit ((ρ • (ContinuousLinearMap.id ℝ H)).comp
      (ρ • (ContinuousLinearMap.id ℝ H)).adjoint) := by
  have hρsq : (ρ ^ (2 : ℕ) : ℝ) ≠ 0 := pow_ne_zero 2 hρ
  rw [show ((ρ • (ContinuousLinearMap.id ℝ H)).comp
      (ρ • (ContinuousLinearMap.id ℝ H)).adjoint) =
      ((ρ ^ (2 : ℕ) : ℝ) • (ContinuousLinearMap.id ℝ H)) by
        ext x
        simp [pow_two, smul_smul]]
  rw [ContinuousLinearMap.isUnit_iff_bijective]
  constructor
  · intro x y hxy
    have hxy' := congrArg (fun z : H ↦ ((ρ ^ (2 : ℕ) : ℝ)⁻¹) • z) hxy
    simpa [smul_smul, inv_mul_cancel₀ hρsq] using hxy'
  · intro y
    refine ⟨((ρ ^ (2 : ℕ) : ℝ)⁻¹) • y, ?_⟩
    simp [smul_smul, inv_mul_cancel₀ hρsq]

/- Source/core/bridge triage:
- `source-facing`: Corollary 23.26 studies the homothetic transport `B = ρ A (ρ·)`.
- `core/canonical`: the owner abstraction for this transport is
  `ContinuousLinearMap.adjointImage`.
- `bridge/view`: the homothety itself is the linear map
  `ρ • (1 : H →L[ℝ] H)`, and the explicit pointwise formula is a view of the
  canonical adjoint-image transport.

Domain-style sampling:
- `Chap16/Proposition_16_6.lean`: `ContinuousLinearMap.adjointImage` is the owner for
  `L^* A L`.
- `Chap23/Definition_23_1.lean`: `J[...]` is the chapter owner for resolvents.
- `Chap23/Proposition_23_17.lean`: `.comp` is the canonical operator-level precomposition API.
- `Chap23/Proposition_23_25.lean`: maximality and resolvent transport for `L.adjointImage A`. -/

/-- Maximal monotonicity part of Corollary 23.26: let `A : H → 2^H` be maximally monotone,
let `ρ ∈ ℝ \ {0}`, and set
`B = ρ A(ρ·)`, realized canonically as
`((ρ • (ContinuousLinearMap.id ℝ H)).adjointImage A)`. Then
`B : H → 2^H` is maximally monotone. -/
theorem maximalMonotone_homothetyImage
    {A : SetValuedOperator H H} (hA : Maximal IsMonotone A) {ρ : ℝ} (hρ : ρ ≠ 0) :
    Maximal IsMonotone ((ρ • (ContinuousLinearMap.id ℝ H)).adjointImage A) :=
  Maximal.adjointImage_of_isUnit_comp_adjoint (ρ • (ContinuousLinearMap.id ℝ H))
    (isUnit_comp_adjoint_homothety hρ) hA

/-- Corollary 23.26 (2): let `A : H → 2^H`, let `ρ ∈ ℝ \ {0}`, and set
`B = ρ A(ρ·)`, realized canonically as
`((ρ • (ContinuousLinearMap.id ℝ H)).adjointImage A)`. Then
`J_B = ρ⁻¹ J_{ρ^2 A}(ρ·)`, formalized on the operator surface as a
precomposition identity. -/
theorem resolvent_homothetyImage_eq_inv_smul_resolvent_sq_smul_precompose
    {A : SetValuedOperator H H} {ρ : ℝ} (hρ : ρ ≠ 0) :
    J[((ρ • (ContinuousLinearMap.id ℝ H)).adjointImage A)] =
      (((ρ⁻¹ : ℝ) • J[((ρ ^ (2 : ℕ)) • A)]).comp (ρ • id.toSetValuedOperator)) := by
  let μ : PosReal := ⟨ρ ^ (2 : ℕ), by simpa [pow_two] using sq_pos_of_ne_zero hρ⟩
  ext x u
  constructor
  · intro hu
    have hu_sub :
        x - u ∈ (1 : ℝ) • ((ρ • (ContinuousLinearMap.id ℝ H)).adjointImage A) u := by
      simpa using
        (mem_resolvent_smul_iff_sub_mem_smul
          ((ρ • (ContinuousLinearMap.id ℝ H)).adjointImage A)
          (1 : PosReal) x u).1 (by simpa using hu)
    rw [one_smul, ContinuousLinearMap.adjointImage_apply, Set.mem_image] at hu_sub
    rcases hu_sub with ⟨a, ha, hxu⟩
    rw [SetValuedOperator.mem_comp]
    refine ⟨ρ • x, ?_, ?_⟩
    · simp [Function.toSetValuedOperator_apply]
    · have hu' : ρ • u ∈ J[((μ : ℝ) • A)] (ρ • x) := by
        have hu_sq : (ρ • x) - ρ • u ∈ (μ : ℝ) • A (ρ • u) := by
          refine Set.mem_smul_set.mpr ?_
          refine ⟨a, ?_, ?_⟩
          · simpa using ha
          · calc
              (μ : ℝ) • a = ((ρ ^ (2 : ℕ)) : ℝ) • a := by rfl
              _ = ρ • ((ρ • (ContinuousLinearMap.id ℝ H)).adjoint a) := by
                    simp [pow_two, smul_smul]
              _ = ρ • (x - u) := by rw [hxu]
              _ = (ρ • x) - ρ • u := by rw [smul_sub]
        exact (mem_resolvent_smul_iff_sub_mem_smul A μ (ρ • x) (ρ • u)).2 hu_sq
      change u ∈ (ρ⁻¹ : ℝ) • J[((ρ ^ (2 : ℕ)) • A)] (ρ • x)
      rw [Set.mem_smul_set_iff_inv_smul_mem₀ (inv_ne_zero hρ)]
      simpa [μ] using hu'
  · intro hu
    rw [SetValuedOperator.mem_comp] at hu
    rcases hu with ⟨y, hy, hu⟩
    simp [Function.toSetValuedOperator_apply] at hy
    subst y
    change u ∈ (ρ⁻¹ : ℝ) • J[((ρ ^ (2 : ℕ)) • A)] (ρ • x) at hu
    rw [Set.mem_smul_set_iff_inv_smul_mem₀ (inv_ne_zero hρ)] at hu
    have hu' : ρ • u ∈ J[((μ : ℝ) • A)] (ρ • x) := by
      simpa [μ] using hu
    have hu_sq : (ρ • x) - ρ • u ∈ (μ : ℝ) • A (ρ • u) := by
      exact (mem_resolvent_smul_iff_sub_mem_smul A μ (ρ • x) (ρ • u)).1 hu'
    rw [Set.mem_smul_set] at hu_sq
    rcases hu_sq with ⟨a, ha, hres⟩
    have hu_sub :
        x - u ∈ (1 : ℝ) • ((ρ • (ContinuousLinearMap.id ℝ H)).adjointImage A) u := by
      rw [one_smul, ContinuousLinearMap.adjointImage_apply, Set.mem_image]
      refine ⟨a, ?_, ?_⟩
      · simpa using ha
      · have hxu' : ρ • (x - u) = ρ • (ρ • a) := by
          calc
            ρ • (x - u) = (ρ • x) - ρ • u := by rw [smul_sub]
            _ = (μ : ℝ) • a := hres.symm
            _ = ρ • (ρ • a) := by simp [μ, pow_two, smul_smul]
        have hxu := congrArg (fun z : H ↦ (ρ⁻¹ : ℝ) • z) hxu'
        simpa [smul_smul, hρ] using hxu.symm
    have hu_res :
        u ∈ J[((1 : ℝ) • ((ρ • (ContinuousLinearMap.id ℝ H)).adjointImage A))] x :=
      (mem_resolvent_smul_iff_sub_mem_smul
        ((ρ • (ContinuousLinearMap.id ℝ H)).adjointImage A) (1 : PosReal) x u).2
          (by simpa using hu_sub)
    simpa using hu_res

end SetValuedOperator
