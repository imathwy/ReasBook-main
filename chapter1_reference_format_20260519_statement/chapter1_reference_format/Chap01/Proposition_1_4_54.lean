import chapter1_reference_format.Chap01.Definition_1_4_53

universe u v

private structure NormCopy (V : Type v) where
  val : V

namespace NormCopy

def equiv (V : Type v) : NormCopy V ≃ V where
  toFun := val
  invFun := fun x ↦ ⟨x⟩
  left_inv x := by cases x; rfl
  right_inv x := rfl

instance {V : Type v} [AddCommMonoid V] : AddCommMonoid (NormCopy V) :=
  (equiv V).addCommMonoid

instance {V : Type v} [AddCommGroup V] : AddCommGroup (NormCopy V) :=
  (equiv V).addCommGroup

instance {K : Type u} {V : Type v} [Semiring K] [AddCommGroup V] [Module K V] :
    Module K (NormCopy V) :=
  Equiv.module K (equiv V)

def linearEquiv (K : Type u) (V : Type v) [Semiring K] [AddCommGroup V] [Module K V] :
    NormCopy V ≃ₗ[K] V where
  __ := equiv V
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

end NormCopy

namespace VectorNorm

section

variable {K : Type u} {V : Type v} [NontriviallyNormedField K] [CompleteSpace K]
  [AddCommGroup V] [Module K V] [FiniteDimensional K V]

/- Proposition 1.4.54 (1): on a finite-dimensional `K`-vector space, any two vector norms are
equivalent in the sense of Definition 1.4.53. This is the source-facing two-norm reformulation of
the canonical continuity of the identity linear equivalence between two normed realizations of the
same finite-dimensional vector space. -/
theorem equivalent_of_finiteDimensional (p q : VectorNorm K V) : Equivalent p q := by
  let q' : VectorNorm K (NormCopy V) :=
    ⟨q.1.comp (NormCopy.linearEquiv K V).toLinearMap, fun x hx ↦ by
      cases x with
      | mk x =>
          have hx' : x = 0 := by
            simpa [NormCopy.linearEquiv, Seminorm.comp_apply] using q.eq_zero_of_map_eq_zero hx
          cases hx'
          rfl⟩
  letI : Norm V := ⟨p.1⟩
  have hpCore : NormedSpace.Core K V := p.toNormedSpaceCore
  letI : NormedAddCommGroup V := NormedAddCommGroup.ofCore hpCore
  letI : NormedSpace K V := NormedSpace.ofCore hpCore
  letI : Norm (NormCopy V) := ⟨q'.1⟩
  have hqCore : NormedSpace.Core K (NormCopy V) := q'.toNormedSpaceCore
  letI : NormedAddCommGroup (NormCopy V) := NormedAddCommGroup.ofCore hqCore
  letI : NormedSpace K (NormCopy V) := NormedSpace.ofCore hqCore
  let e : V ≃L[K] NormCopy V := (NormCopy.linearEquiv K V).symm.toContinuousLinearEquiv
  let C : ℝ := max (max ‖(e : V →L[K] NormCopy V)‖ ‖(e.symm : NormCopy V →L[K] V)‖) 2
  refine ⟨C, lt_of_lt_of_le one_lt_two (le_max_right _ _), fun x ↦ ?_⟩
  constructor
  · rw [inv_mul_le_iff₀ (lt_trans zero_lt_one (lt_of_lt_of_le one_lt_two (le_max_right _ _)))]
    calc
      p x ≤ ‖(e.symm : NormCopy V →L[K] V)‖ * q x := by
        simpa [e, q', Seminorm.comp_apply] using
          (e.symm : NormCopy V →L[K] V).le_opNorm ⟨x⟩
      _ ≤ C * q x := by
        gcongr
        exact le_trans (le_max_right _ _) (le_max_left _ _)
  · calc
      q x ≤ ‖(e : V →L[K] NormCopy V)‖ * p x := by
        simpa [e, q', Seminorm.comp_apply] using
          (e : V →L[K] NormCopy V).le_opNorm x
      _ ≤ C * p x := by
        gcongr
        exact le_trans (le_max_left _ _) (le_max_left _ _)

/- Proposition 1.4.54 (2): after installing the normed-space structure defined by a chosen vector
norm `p`, a finite-dimensional `K`-vector space is complete. This is the source-facing arbitrary-
norm specialization of `FiniteDimensional.complete`. -/
theorem completeSpace (p : VectorNorm K V) :
    let _ : Norm V := ⟨p.1⟩
    let _ : NormedAddCommGroup V := p.toNormedAddCommGroup
    let _ : NormedSpace K V := p.toNormedSpace
    CompleteSpace V := by
  letI : Norm V := ⟨p.1⟩
  letI : NormedAddCommGroup V := p.toNormedAddCommGroup
  letI : NormedSpace K V := p.toNormedSpace
  exact FiniteDimensional.complete K V

end

end VectorNorm
