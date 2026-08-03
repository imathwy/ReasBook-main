import BauschkeLean.Chap23.Proposition_23_8

-- Semantic recall note: `lean_leansearch` returned only unrelated spectrum-resolvent results, so
-- this file follows the verified local Chapter 23 owners `J[...]`, `ofFunction`,
-- `IsMonotone`, and `Maximal IsMonotone`.

open scoped Pointwise SetValuedOperator

universe u

namespace SetValuedOperator

section Algebraic

/-
The owner abstraction in this file is the Chapter 23 resolvent `J[...]` together with the
Chapter 16 singleton operator `id.toSetValuedOperator`. Proposition 23.10(1) rewrites `A` as the
set-valued difference `J[A]⁻¹ - Id`, and that source-facing identity genuinely uses commutative
additive cancellation. The operator expression itself typechecks over `[AddGroup H]`, but the
equality is not valid in general noncommutative additive groups.
-/
variable {H : Type u} [AddCommGroup H]

/-- Proposition 23.10 (1): every set-valued operator is recovered from its resolvent by
`A = J[A]⁻¹ - Id`, formalized in the commutative additive setting as
`A = (J[A])⁻¹ - id.toSetValuedOperator`. -/
theorem eq_inverse_resolvent_sub_id
    (A : SetValuedOperator H H) :
    A = ((J[A])⁻¹ - id.toSetValuedOperator) := by
  ext x u
  constructor
  · intro hu
    rw [Pi.sub_apply, Set.mem_sub]
    refine ⟨x + u, ?_, x, by simp [Function.toSetValuedOperator_apply], ?_⟩
    · rw [mem_inverse_iff, resolvent_def, mem_inverse_iff]
      change x + u ∈ ((id : H → H).toSetValuedOperator x + A x)
      rw [Function.toSetValuedOperator_apply, Set.mem_add]
      exact ⟨x, by simp, u, hu, by abel_nf⟩
    · abel_nf
  · rw [Pi.sub_apply, Set.mem_sub]
    rintro ⟨y, hy, z, hz, huz⟩
    rw [Function.toSetValuedOperator_apply, Set.mem_singleton_iff] at hz
    subst z
    rw [mem_inverse_iff, resolvent_def, mem_inverse_iff] at hy
    change y ∈ ((id : H → H).toSetValuedOperator x + A x) at hy
    rw [Function.toSetValuedOperator_apply, Set.mem_add] at hy
    rcases hy with ⟨z, hz, v, hv, hyv⟩
    rw [Set.mem_singleton_iff] at hz
    subst z
    have hyvx : y - x = v := by
      rw [← hyv]
      change x + v - x = v
      abel_nf
    have huv : u = v := by
      calc
        u = y - x := by simpa using huz.symm
        _ = v := hyvx
    simpa [huv] using hv

/-- Proposition 23.10 (1): if `T : D → H` realizes the restricted resolvent `J[A]` through
`J[A] = ofFunction D T`, then `A = T⁻¹ - Id`, formalized as
`A = ((ofFunction D T)⁻¹ - id.toSetValuedOperator)` in the same commutative additive setting. -/
theorem eq_sub_id_inverse_ofFunction_of_resolvent_eq_ofFunction
    (A : SetValuedOperator H H) (D : Set H)
    (T : D → H) (hJ : J[A] = ofFunction D T) :
    A = ((ofFunction D T)⁻¹ - id.toSetValuedOperator) := by
  calc
    A = ((J[A])⁻¹ - id.toSetValuedOperator) := eq_inverse_resolvent_sub_id A
    _ = ((ofFunction D T)⁻¹ - id.toSetValuedOperator) := by rw [hJ]

end Algebraic

section Hilbert

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

/-- Proposition 23.10 (2): if `T : D → H` realizes the restricted resolvent `J[A]` through
`J[A] = ofFunction D T`, then `A` is monotone if and only if `T` is firmly nonexpansive on
`D`. -/
theorem isMonotone_iff_firmlyNonexpansiveOn_of_resolvent_eq_ofFunction
    (A : SetValuedOperator H H) (D : Set H)
    (T : D → H) (hJ : J[A] = ofFunction D T) :
    A.IsMonotone ↔ FirmlyNonexpansiveOn D T := by
  rw [eq_sub_id_inverse_ofFunction_of_resolvent_eq_ofFunction A D T hJ]
  simpa using (firmlyNonexpansiveOn_iff_isMonotone_sub_id_inverse_ofFunction D T).symm

/-- Proposition 23.10 (3): if `T : D → H` realizes the restricted resolvent `J[A]` through
`J[A] = ofFunction D T`, then `A` is maximally monotone if and only if `T` is firmly
nonexpansive on `D` and `D = H`, formalized as `D = Set.univ`. -/
theorem maximal_isMonotone_iff_firmlyNonexpansiveOn_and_univ_of_resolvent_eq_ofFunction
    (A : SetValuedOperator H H) (D : Set H)
    (T : D → H) (hJ : J[A] = ofFunction D T) :
    Maximal IsMonotone A ↔ FirmlyNonexpansiveOn D T ∧ D = Set.univ := by
  rw [eq_sub_id_inverse_ofFunction_of_resolvent_eq_ofFunction A D T hJ]
  simpa using (firmlyNonexpansiveOn_and_univ_iff_maximal_sub_id_inverse_ofFunction D T).symm

end Hilbert

end SetValuedOperator
