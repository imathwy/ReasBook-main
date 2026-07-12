import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open Cardinal Polynomial

universe u v

section

variable {k : Type u} {V : Type v} [Field k] [AddCommGroup V] [Module k V] [Nontrivial V]

/-- Helper for Lemma 10.35.10: if every monic polynomial in `T` is invertible, then every nonzero
polynomial in `T` is invertible after normalizing by its leading coefficient. -/
lemma aeval_isUnit_of_forall_monic_aeval_isUnit
    (T : Module.End k V)
    (hmonic : ∀ P : k[X], P.Monic → IsUnit (aeval T P)) :
    ∀ P : k[X], P ≠ 0 → IsUnit (aeval T P) := by
  intro P hP
  -- Normalize by the leading coefficient so the monic hypothesis applies.
  have hmonicP : (P * C P.leadingCoeff⁻¹).Monic := monic_mul_leadingCoeff_inv hP
  have hunit_norm : IsUnit (aeval T (P * C P.leadingCoeff⁻¹)) := hmonic _ hmonicP
  have hcomm :
      Commute ((aeval T) P) ((algebraMap k (Module.End k V)) P.leadingCoeff⁻¹) :=
    (Algebra.commutes _ _).symm
  -- Strip off the invertible scalar factor on the right.
  have hunit_product :
      IsUnit (((aeval T) P) * ((algebraMap k (Module.End k V)) P.leadingCoeff⁻¹)) := by
    simpa [map_mul] using hunit_norm
  exact (hcomm.isUnit_mul_iff.mp hunit_product).1

/-- Helper for Lemma 10.35.10: chosen preimages of a fixed nonzero vector under the invertible maps
`aeval T (X - C a)` form a linearly independent family. -/
lemma linearIndependent_preimage_family_of_forall_aeval_isUnit
    (T : Module.End k V)
    (hunit : ∀ P : k[X], P ≠ 0 → IsUnit (aeval T P))
    {v : V} (hv : v ≠ 0) :
    LinearIndependent k fun a : k ↦
      (LinearMap.GeneralLinearGroup.toLinearEquiv
        ((hunit (X - C a) (X_sub_C_ne_zero a)).unit)).symm v := by
  classical
  let w : k → V := fun a ↦
    (LinearMap.GeneralLinearGroup.toLinearEquiv
      ((hunit (X - C a) (X_sub_C_ne_zero a)).unit)).symm v
  have hw : ∀ a : k, (aeval T (X - C a)) (w a) = v := by
    intro a
    -- Each `w a` is chosen to be a preimage of `v` under `aeval T (X - C a)`.
    change
      (LinearMap.GeneralLinearGroup.toLinearEquiv
        ((hunit (X - C a) (X_sub_C_ne_zero a)).unit))
        ((LinearMap.GeneralLinearGroup.toLinearEquiv
          ((hunit (X - C a) (X_sub_C_ne_zero a)).unit)).symm v) = v
    exact LinearEquiv.apply_symm_apply _ _
  rw [linearIndependent_iff']
  intro s m hm i hi
  let q : k[X] := s.prod fun j ↦ X - C j
  let p : k[X] := s.sum fun j ↦ C (m j) * (s.erase j).prod fun x ↦ X - C x
  have hq_apply :
      ∀ j ∈ s, (aeval T q) (w j) = (aeval T ((s.erase j).prod fun x ↦ X - C x)) v := by
    intro j hj
    -- Factor the product polynomial into the `j`-term and the remaining factors.
    have hwj := congrArg
      (fun x : V ↦ (aeval T ((s.erase j).prod fun x ↦ X - C x)) x) (hw j)
    simpa [q, ← s.prod_erase_mul _ hj, aeval_mul, Module.End.mul_apply] using hwj
  have hm_apply : ∑ j ∈ s, m j • (aeval T q) (w j) = 0 := by
    -- Apply `aeval T q` to the assumed linear relation.
    simpa [w, map_sum, map_smul] using congrArg (fun x : V ↦ (aeval T q) x) hm
  have hp_apply : (aeval T p) v = 0 := by
    -- Repackage the transformed relation as a single polynomial evaluated at `T`.
    calc
      (aeval T p) v
          = ∑ j ∈ s, m j • (aeval T ((s.erase j).prod fun x ↦ X - C x)) v := by
              simp [p, map_sum, map_mul, aeval_C, Module.End.mul_apply]
      _ = ∑ j ∈ s, m j • (aeval T q) (w j) := by
            refine Finset.sum_congr rfl ?_
            intro j hj
            rw [hq_apply j hj]
      _ = 0 := hm_apply
  have hp_zero : p = 0 := by
    by_cases hp : p = 0
    · exact hp
    · -- A nonzero `p` would make `aeval T p` invertible, forcing `v = 0`.
      have hinj : Function.Injective (aeval T p) :=
        (LinearMap.GeneralLinearGroup.toLinearEquiv ((hunit p hp).unit)).injective
      have hv_zero : v = 0 := hinj <| by simpa using hp_apply
      exact False.elim (hv hv_zero)
  have h_eval_zero : Polynomial.aeval i p = 0 := by
    -- Evaluate the zero polynomial at `i` to isolate the coefficient `m i`.
    simpa [hp_zero] using congrArg (Polynomial.aeval i) hp_zero
  have h_other :
      ∀ j ∈ s.erase i, m j * ((s.erase j).prod fun x ↦ i - x) = 0 := by
    intro j hj
    have hij : i ∈ s.erase j := Finset.mem_erase_of_ne_of_mem (Finset.ne_of_mem_erase hj).symm hi
    rw [← (s.erase j).prod_erase_mul (fun x ↦ i - x) hij]
    simp
  have h_eval_sum : ∑ j ∈ s, m j * ((s.erase j).prod fun x ↦ i - x) = 0 := by
    -- Expanding `aeval i p` turns the polynomial identity into a scalar relation.
    simpa [p, map_zero, map_sum, map_mul, aeval_X, aeval_C, Algebra.algebraMap_self_apply] using
      h_eval_zero
  have hmi :
      m i * ((s.erase i).prod fun x ↦ i - x) = 0 := by
    -- All other summands vanish because they retain the factor `i - i`.
    rw [← s.sum_erase_add (fun j ↦ m j * ((s.erase j).prod fun x ↦ i - x)) hi,
      Finset.sum_eq_zero h_other, zero_add] at h_eval_sum
    exact h_eval_sum
  -- The remaining product is nonzero because all roots are distinct.
  exact eq_zero_of_ne_zero_of_mul_right_eq_zero
    (Finset.prod_ne_zero_iff.2 fun j hj ↦ sub_ne_zero.2 (Finset.ne_of_mem_erase hj).symm) hmi

/-- Helper for Lemma 10.35.10: if every nonzero polynomial in `T` is invertible, then the rank of
`V` is at least the cardinality of `k`. -/
lemma rank_ge_cardinal_of_forall_aeval_isUnit
    (T : Module.End k V)
    (hunit : ∀ P : k[X], P ≠ 0 → IsUnit (aeval T P)) :
    lift.{max u v} (#k) ≤ lift.{max u v} (Module.rank k V) := by
  obtain ⟨v, hv⟩ := exists_ne (0 : V)
  -- A `k`-indexed linearly independent family forces the rank lower bound.
  simpa [← Cardinal.lift_umax] using
    (linearIndependent_preimage_family_of_forall_aeval_isUnit (T := T) hunit hv).cardinal_lift_le_rank

/-- Lemma 10.35.10 (Tag 00FT): if `V` is a nontrivial `k`-vector space whose dimension is
strictly smaller than the cardinality of `k`, then every endomorphism of `V` admits a monic
polynomial whose evaluation at that endomorphism is not a unit. -/
@[stacks 00FT]
theorem exists_monic_polynomial_aeval_not_isUnit_of_rank_lt_cardinal
    (T : Module.End k V)
    (hV : lift.{max u v} (Module.rank k V) < lift.{max u v} (#k)) :
    ∃ P : k[X], P.Monic ∧ ¬ IsUnit (aeval T P) := by
  classical
  by_contra h
  push Not at h
  -- Route correction: the direct source proof uses a rank contradiction, not algebraicity.
  have hunit : ∀ P : k[X], P ≠ 0 → IsUnit (aeval T P) :=
    aeval_isUnit_of_forall_monic_aeval_isUnit (T := T) h
  have hrank : lift.{max u v} (#k) ≤ lift.{max u v} (Module.rank k V) :=
    rank_ge_cardinal_of_forall_aeval_isUnit (T := T) hunit
  exact not_lt_of_ge hrank hV

end
