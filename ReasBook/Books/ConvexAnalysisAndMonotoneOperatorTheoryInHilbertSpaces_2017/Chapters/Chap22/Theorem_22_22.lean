import BauschkeLean.Chap22.Definition_22_13
import BauschkeLean.Chap22.Proposition_22_21

-- Declarations for this item will be appended below by the statement pipeline.

namespace SetValuedOperator

-- Domain sampling:
-- `source-facing`: Theorem 22.22 is the one-dimensional equivalence between monotonicity and
-- cyclic monotonicity.
-- `core/canonical`: the owner predicates are `SetValuedOperator.IsMonotone` and
-- `SetValuedOperator.IsCyclicallyMonotone`.
-- `bridge/view`: Proposition 22.21 supplies the order-theoretic graph-chain bridge, and the proof
-- below upgrades that bridge to cyclic monotonicity via mathlib's rearrangement inequality.

/-- On the real line, a monotone set-valued operator is cyclically monotone. -/
theorem IsMonotone.isCyclicallyMonotone
    {A : SetValuedOperator ℝ ℝ} (hA : A.IsMonotone) :
    A.IsCyclicallyMonotone := by
  refine ⟨fun {n} hn ↦ ?_⟩
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le hn
  refine ⟨by omega, ?_⟩
  intro x u hu hxn
  let xf : Fin (2 + m) → ℝ := fun i ↦ x i
  let uf : Fin (2 + m) → ℝ := fun i ↦ u i
  let p : Fin (2 + m) := ⟨1 + m, by omega⟩
  let σ : Equiv.Perm (Fin (2 + m)) := Fin.cycleRange p
  have hchain : IsChain (· ≤ ·) (gra A) :=
    (isMonotone_iff_graph_isChain A).1 hA
  have hmono_fu : Monovary xf uf := by
    intro i j hij
    have hcmp : (x i, u i) ≤ (x j, u j) ∨ (x j, u j) ≤ (x i, u i) := by
      by_cases hneq : (x i, u i) = (x j, u j)
      · exact Or.inl (by simp [hneq])
      · exact hchain (by simpa [SetValuedOperator.mem_graph] using hu i i.2)
          (by simpa [SetValuedOperator.mem_graph] using hu j j.2) hneq
    rcases hcmp with hij' | hji'
    · exact hij'.1
    · exact (not_lt_of_ge hji'.2 hij).elim
  have hσ_apply (i : Fin (2 + m)) : σ i = if i = p then 0 else i + 1 := by
    by_cases hip : i = p
    · subst hip
      dsimp [σ, p]
      rw [Fin.cycleRange_apply]
      simp
    · have hi_le : i ≤ p := by
        change (i : ℕ) ≤ 1 + m
        omega
      have hi_lt : i < p := lt_of_le_of_ne hi_le hip
      dsimp [σ]
      rw [Fin.cycleRange_apply]
      simp [hi_lt, hip]
  have hperm : ∑ i : Fin (2 + m), xf (σ i) * uf i ≤ ∑ i : Fin (2 + m), xf i * uf i :=
    Monovary.sum_comp_perm_mul_le_sum_mul hmono_fu
  have hperm' : ∑ i : Fin (2 + m), (xf (σ i) - xf i) * uf i ≤ 0 := by
    simpa [Finset.sum_sub_distrib, sub_mul] using sub_nonpos.mpr hperm
  have hperm'' := by
    simpa [Finset.sum_fin_eq_sum_range, xf, uf, p, hσ_apply] using hperm'
  refine le_of_eq_of_le ?_ hperm''
  apply Finset.sum_congr rfl
  intro i hi
  have hi_lt : i < 2 + m := Finset.mem_range.mp hi
  by_cases hip : i = 1 + m
  · subst hip
    have hidx : 1 + m + 1 = 2 + m := by omega
    have hx_last : x (1 + m + 1) = x 0 := by
      simpa [hidx] using hxn
    have hinner_last :
        inner ℝ (x (1 + m + 1) - x (1 + m)) (u (1 + m)) =
          (x (1 + m + 1) - x (1 + m)) * u (1 + m) := by
      simpa [conj_trivial] using
        (RCLike.inner_apply' (x (1 + m + 1) - x (1 + m)) (u (1 + m)))
    rw [hinner_last]
    rw [hx_last]
    simp [hi_lt]
  · have hinner :
        inner ℝ (x (i + 1) - x i) (u i) = (x (i + 1) - x i) * u i := by
      simpa [conj_trivial] using (RCLike.inner_apply' (x (i + 1) - x i) (u i))
    rw [hinner]
    have hi_succ_lt : i + 1 < 2 + m := by
      omega
    simp [hi_lt, hip]
    simp [Fin.val_add, Nat.mod_eq_of_lt hi_succ_lt]

-- The source's nonempty-graph hypothesis is redundant for the canonical owner-level equivalence.
/-- Theorem 22.22: a set-valued operator `A : ℝ → 2^ℝ` is monotone if and only if it is
cyclically monotone. -/
theorem isMonotone_iff_isCyclicallyMonotone
    (A : SetValuedOperator ℝ ℝ) :
    A.IsMonotone ↔ A.IsCyclicallyMonotone := by
  constructor
  · exact IsMonotone.isCyclicallyMonotone
  · exact IsCyclicallyMonotone.isMonotone

end SetValuedOperator
