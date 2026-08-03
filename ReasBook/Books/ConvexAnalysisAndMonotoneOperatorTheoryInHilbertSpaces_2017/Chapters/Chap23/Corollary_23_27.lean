import BauschkeLean.Chap23.Proposition_23_25

open scoped InnerProductSpace Pointwise SetValuedOperator
open ERealFunction

universe u

namespace SetValuedOperator

/- Source/core/bridge triage:
- `source-facing`: Corollary 23.27 specializes the conjugate transport `B = L^* A L`
  to the orthogonal case `L⁻¹ = L*`.
- `core/canonical`: the reusable Chapter 23 owners are `Maximal IsMonotone`, `J[...]`, and the
  adjoint-image bridge `ContinuousLinearMap.adjointImage`.
- `bridge/view`: the orthogonal hypothesis is used only to identify `L.comp L.adjoint` and
  `L.adjoint.comp L` with `1`, so the corollary can reuse Proposition 23.25 directly.

Domain-style sampling:
- `Chap16/Proposition_16_6.lean`: `ContinuousLinearMap.adjointImage` is the canonical owner for
  `L^* A L`.
- `Chap23/Proposition_23_25.lean`: the maximality transport for `L.adjointImage A` is already
  phrased through `IsUnit (L.comp L.adjoint)`.
- `Chap24/Proposition_24_8.lean`: nearby Chapter 24 results use the same specialization
  `(hL : L.IsInvertible)` and `(hLadj : L.inverse = L.adjoint)`. -/

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

section InvertibleAdjoint

variable {L : H →L[ℝ] H} (hL : L.IsInvertible) (hLadj : L.inverse = L.adjoint)

/-- Helper for Corollary 23.27: the orthogonal hypothesis `L.inverse = L.adjoint`
identifies `L.comp L.adjoint` with the identity operator. -/
private theorem comp_adjoint_eq_one_of_inverse_eq_adjoint
    (hL : L.IsInvertible) (hLadj : L.inverse = L.adjoint)
    : L.comp L.adjoint = (1 : H →L[ℝ] H) := by
  -- Replace `L.adjoint` with the inverse and use the left inverse identity pointwise.
  ext x
  rw [← hLadj]
  simpa using hL.self_apply_inverse x

/-- Helper for Corollary 23.27: the same orthogonal hypothesis also identifies
`L.adjoint.comp L` with the identity operator. -/
private theorem adjoint_comp_eq_one_of_inverse_eq_adjoint
    (hL : L.IsInvertible) (hLadj : L.inverse = L.adjoint) :
    L.adjoint.comp L = (1 : H →L[ℝ] H) := by
  -- Replace `L.adjoint` with the inverse and use the right inverse identity pointwise.
  ext x
  rw [← hLadj]
  simpa using hL.inverse_apply_self x

/-- Helper for Corollary 23.27: Proposition 23.25 asks for `IsUnit (L.comp L.adjoint)`,
and the orthogonal bridge reduces this to `IsUnit 1`. -/
private theorem isUnit_comp_adjoint_of_inverse_eq_adjoint
    (hL : L.IsInvertible) (hLadj : L.inverse = L.adjoint)
    : IsUnit (L.comp L.adjoint) := by
  -- Normalize the composite to the identity operator, then close by simplification.
  rw [comp_adjoint_eq_one_of_inverse_eq_adjoint hL hLadj]
  simp

/-- Maximality part of Corollary 23.27: let `A : H → 2^H` be maximally monotone, let
`L : H →L[ℝ] H` be invertible with inverse `L.adjoint`, and set `B = L^* A L`, realized as
`L.adjointImage A`. Then `B` is maximally monotone. -/
theorem Maximal.adjointImage_of_isInvertible_of_inverse_eq_adjoint
    {A : SetValuedOperator H H} (hA : Maximal IsMonotone A)
    (L : H →L[ℝ] H) (hL : L.IsInvertible) (hLadj : L.inverse = L.adjoint) :
    Maximal IsMonotone (L.adjointImage A) :=
  Maximal.adjointImage_of_isUnit_comp_adjoint L
    (isUnit_comp_adjoint_of_inverse_eq_adjoint hL hLadj) hA

/-- Helper for Corollary 23.27: the left orthogonal cancellation
`L (L.adjoint x) = x` obtained from the operator identity above. -/
private theorem comp_adjoint_apply_eq_self_of_inverse_eq_adjoint
    (hL : L.IsInvertible) (hLadj : L.inverse = L.adjoint)
    (x : H) : L (L.adjoint x) = x := by
  -- Evaluate the operator equality from `comp_adjoint_eq_one_of_inverse_eq_adjoint` at `x`.
  have hLLstar := comp_adjoint_eq_one_of_inverse_eq_adjoint hL hLadj
  simpa using congrArg (fun T : H →L[ℝ] H ↦ T x) hLLstar

/-- Helper for Corollary 23.27: the right orthogonal cancellation
`L.adjoint (L x) = x` obtained from the operator identity above. -/
private theorem adjoint_comp_apply_eq_self_of_inverse_eq_adjoint
    (hL : L.IsInvertible) (hLadj : L.inverse = L.adjoint)
    (x : H) : L.adjoint (L x) = x := by
  -- Evaluate the operator equality from `adjoint_comp_eq_one_of_inverse_eq_adjoint` at `x`.
  have hstarL := adjoint_comp_eq_one_of_inverse_eq_adjoint hL hLadj
  simpa using congrArg (fun T : H →L[ℝ] H ↦ T x) hstarL

/-- Corollary 23.27: if `B = L^* A L`, realized as `L.adjointImage A`, and `L⁻¹ = L*`, then
the resolvent satisfies `J_B = L^* ∘ J_A ∘ L`, formalized as
`J[(L.adjointImage A)] = L.adjointImage J[A]`. -/
theorem resolvent_adjointImage_eq_adjointImage_resolvent_of_isInvertible_of_inverse_eq_adjoint
    (A : SetValuedOperator H H)
    (L : H →L[ℝ] H) (hL : L.IsInvertible) (hLadj : L.inverse = L.adjoint) :
    J[(L.adjointImage A)] = L.adjointImage J[A] := by
  -- Route correction: instead of normalizing the whole operator algebraically, transport the
  -- resolvent witness across `L` and `L.adjoint` pointwise using the orthogonal cancellations.
  ext x u
  constructor
  · intro hu
    -- Read `u ∈ J[L.adjointImage A] x` as a resolvent witness for `x - u`.
    have hu_sub : x - u ∈ (1 : ℝ) • (L.adjointImage A) u := by
      simpa using
        (mem_resolvent_smul_iff_sub_mem_smul (L.adjointImage A) (1 : PosReal) x u).1
          (by simpa using hu)
    rw [one_smul, ContinuousLinearMap.adjointImage_apply, Set.mem_image] at hu_sub
    rcases hu_sub with ⟨a, ha, hxu⟩
    rw [ContinuousLinearMap.adjointImage_apply, Set.mem_image]
    refine ⟨L u, ?_, ?_⟩
    · have hLxu : L x - L u = a := by
        -- Apply `L` to the affine witness and cancel the intermediate `L.adjoint`.
        calc
          L x - L u = L (x - u) := by rw [ContinuousLinearMap.map_sub]
          _ = L (L.adjoint a) := by rw [← hxu]
          _ = a := comp_adjoint_apply_eq_self_of_inverse_eq_adjoint hL hLadj a
      have hLu_sub : L x - L u ∈ (1 : ℝ) • A (L u) := by
        simpa [one_smul, hLxu] using ha
      -- Repackage the transported witness as resolvent membership for `A`.
      simpa using
        (mem_resolvent_smul_iff_sub_mem_smul A (1 : PosReal) (L x) (L u)).2 hLu_sub
    · rw [← hLadj]
      exact hL.inverse_apply_self u
  · intro hu
    -- Unpack the transported resolvent witness `u = L.adjoint p` from the right-hand side.
    rw [ContinuousLinearMap.adjointImage_apply, Set.mem_image] at hu
    rcases hu with ⟨p, hp, hu⟩
    have hp_sub : L x - p ∈ (1 : ℝ) • A p := by
      simpa using
        (mem_resolvent_smul_iff_sub_mem_smul A (1 : PosReal) (L x) p).1 (by simpa using hp)
    have hLp : L (L.adjoint p) = p :=
      comp_adjoint_apply_eq_self_of_inverse_eq_adjoint hL hLadj p
    have hLu : L u = p := by
      rw [← hu]
      exact hLp
    have hx : L.adjoint (L x) = x :=
      adjoint_comp_apply_eq_self_of_inverse_eq_adjoint hL hLadj x
    have hu_sub : x - u ∈ (1 : ℝ) • (L.adjointImage A) u := by
      -- Apply `L.adjoint` to the transported affine witness and cancel `L`.
      rw [one_smul, ContinuousLinearMap.adjointImage_apply, Set.mem_image]
      refine ⟨L x - p, ?_, ?_⟩
      · simpa [one_smul, hLu] using hp_sub
      · calc
          L.adjoint (L x - p) = L.adjoint (L x) - L.adjoint p := by
            rw [ContinuousLinearMap.map_sub]
          _ = x - u := by simp [hx, hu]
    -- Close by converting the transported witness back into resolvent membership.
    simpa using
      (mem_resolvent_smul_iff_sub_mem_smul (L.adjointImage A) (1 : PosReal) x u).2 hu_sub

end InvertibleAdjoint

end SetValuedOperator
