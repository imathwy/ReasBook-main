import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

section

open AdicCompletion

variable (R : Type u) [CommRing R]
variable (I J : Ideal R)
variable (M : Type v) [AddCommGroup M] [Module R M]

private theorem isAdicComplete_completion_right_of_pow_le
    (c d : ℕ) (hc : 0 < c) (hd : 0 < d) (hIJ : I ^ c ≤ J) (hJI : J ^ d ≤ I) :
    IsAdicComplete I (AdicCompletion J M) :=
  (AdicCompletion.of_bijective_iff).mp sorry

private theorem isAdicComplete_completion_left_of_pow_le
    (c d : ℕ) (hc : 0 < c) (hd : 0 < d) (hIJ : I ^ c ≤ J) (hJI : J ^ d ≤ I) :
    IsAdicComplete J (AdicCompletion I M) :=
  (AdicCompletion.of_bijective_iff).mp sorry

private noncomputable def adicCompletionToRightOfPowLe :
    (c d : ℕ) → (hc : 0 < c) → (hd : 0 < d) → (hIJ : I ^ c ≤ J) → (hJI : J ^ d ≤ I) →
      AdicCompletion I M →ₗ[R] AdicCompletion J M
  | c, d, hc, hd, hIJ, hJI =>
  let _ : IsAdicComplete I (AdicCompletion J M) :=
    isAdicComplete_completion_right_of_pow_le R I J M c d hc hd hIJ hJI
  ((ofLinearEquiv I (AdicCompletion J M)).symm : _).toLinearMap.comp
    ((AdicCompletion.map I (of J M)).restrictScalars R)

private noncomputable def adicCompletionToLeftOfPowLe :
    (c d : ℕ) → (hc : 0 < c) → (hd : 0 < d) → (hIJ : I ^ c ≤ J) → (hJI : J ^ d ≤ I) →
      AdicCompletion J M →ₗ[R] AdicCompletion I M
  | c, d, hc, hd, hIJ, hJI =>
  let _ : IsAdicComplete J (AdicCompletion I M) :=
    isAdicComplete_completion_left_of_pow_le R I J M c d hc hd hIJ hJI
  ((ofLinearEquiv J (AdicCompletion I M)).symm : _).toLinearMap.comp
    ((AdicCompletion.map J (of I M)).restrictScalars R)

@[simp]
private theorem adicCompletionToRightOfPowLe_of
    (c d : ℕ) (hc : 0 < c) (hd : 0 < d) (hIJ : I ^ c ≤ J) (hJI : J ^ d ≤ I) (x : M) :
    adicCompletionToRightOfPowLe R I J M c d hc hd hIJ hJI (of I M x) = of J M x := by
  let _ : IsAdicComplete I (AdicCompletion J M) :=
    isAdicComplete_completion_right_of_pow_le R I J M c d hc hd hIJ hJI
  rw [adicCompletionToRightOfPowLe, LinearMap.comp_apply, LinearMap.restrictScalars_apply,
    AdicCompletion.map_of]
  simp

@[simp]
private theorem adicCompletionToLeftOfPowLe_of
    (c d : ℕ) (hc : 0 < c) (hd : 0 < d) (hIJ : I ^ c ≤ J) (hJI : J ^ d ≤ I) (x : M) :
    adicCompletionToLeftOfPowLe R I J M c d hc hd hIJ hJI (of J M x) = of I M x := by
  let _ : IsAdicComplete J (AdicCompletion I M) :=
    isAdicComplete_completion_left_of_pow_le R I J M c d hc hd hIJ hJI
  rw [adicCompletionToLeftOfPowLe, LinearMap.comp_apply, LinearMap.restrictScalars_apply,
    AdicCompletion.map_of]
  simp

-- Proof sketch: the power containments `I ^ c ≤ J` and `J ^ d ≤ I` make the `I`-adic and
-- `J`-adic filtrations cofinal. Hence each completion is complete for the other filtration, so the
-- canonical maps `M → AdicCompletion I M` and `M → AdicCompletion J M` induce mutually inverse
-- comparison morphisms between the two completions.
/-- Lemma 10.96.9: if positive powers of `I` and `J` contain one another, then the `I`-adic and
`J`-adic completions of any `R`-module are canonically identified. -/
noncomputable def adicCompletionLinearEquivOfPowLe :
    (c d : ℕ) → (hc : 0 < c) → (hd : 0 < d) → (hIJ : I ^ c ≤ J) → (hJI : J ^ d ≤ I) →
      AdicCompletion I M ≃ₗ[R] AdicCompletion J M
  | c, d, hc, hd, hIJ, hJI =>
  LinearEquiv.ofLinear
    (adicCompletionToRightOfPowLe R I J M c d hc hd hIJ hJI)
    (adicCompletionToLeftOfPowLe R I J M c d hc hd hIJ hJI)
    (by
      ext x
      sorry)
    (by
      ext x
      sorry)

@[simp]
theorem adicCompletionLinearEquivOfPowLe_of
    (c d : ℕ) (hc : 0 < c) (hd : 0 < d) (hIJ : I ^ c ≤ J) (hJI : J ^ d ≤ I) (x : M) :
    adicCompletionLinearEquivOfPowLe R I J M c d hc hd hIJ hJI (of I M x) = of J M x := by
  exact adicCompletionToRightOfPowLe_of R I J M c d hc hd hIJ hJI x

-- Proof sketch: use the direct comparison equivalence of the two completion functors together with
-- `AdicCompletion.of_bijective_iff`, which identifies adic completeness with bijectivity of the
-- canonical map to the completion.
/-- Under mutual positive-power containments between `I` and `J`, an `R`-module is `I`-adically
complete if and only if it is `J`-adically complete. -/
theorem isAdicComplete_iff_of_pow_le :
    (c d : ℕ) → (hc : 0 < c) → (hd : 0 < d) → (hIJ : I ^ c ≤ J) → (hJI : J ^ d ≤ I) →
      IsAdicComplete I M ↔ IsAdicComplete J M
  | c, d, hc, hd, hIJ, hJI => by
      sorry

end
