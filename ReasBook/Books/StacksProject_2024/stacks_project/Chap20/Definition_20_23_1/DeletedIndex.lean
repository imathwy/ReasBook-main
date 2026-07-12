import Mathlib.GroupTheory.Perm.Fin
import Mathlib.Tactic

noncomputable section

/-- Helper for Definition 20.23.1: after deleting the source index `j` and the target index
`τ j`, the remaining action of `τ` on the smaller finite set is the permutation obtained by
moving both deleted positions to `0` and reading the `Fin`-decomposition there. -/
abbrev deleted_index_perm {p : ℕ} (τ : Equiv.Perm (Fin (p + 2))) (j : Fin (p + 2)) :
    Equiv.Perm (Fin (p + 1)) :=
  (Equiv.Perm.decomposeFin ((τ j).cycleRange * τ * j.cycleRange.symm)).2

/-- Helper for Definition 20.23.1: deleting the source index `j` and then applying `τ`
is the same as first applying the deleted-index permutation on the smaller tuple and then
reinserting the target index `τ j`. -/
theorem deleted_index_perm_comp_succAbove {p : ℕ} (τ : Equiv.Perm (Fin (p + 2)))
    (j : Fin (p + 2)) :
    τ ∘ j.succAboveEmb = (τ j).succAboveEmb ∘ deleted_index_perm τ j := by
  let e : Equiv.Perm (Fin (p + 2)) := (τ j).cycleRange * τ * j.cycleRange.symm
  have hdecomp : Equiv.Perm.decomposeFin e = (0, deleted_index_perm τ j) := by
    ext <;> simp [deleted_index_perm, e, Equiv.Perm.decomposeFin]
  have he :
      Equiv.Perm.decomposeFin.symm (0, deleted_index_perm τ j) = e := by
    apply (Equiv.Perm.decomposeFin).injective
    simpa using hdecomp.symm
  ext k
  have hk :
      e k.succ = (deleted_index_perm τ j k).succ := by
    rw [← he, Equiv.Perm.decomposeFin_symm_apply_succ]
    simp
  have hk' := congrArg (fun x ↦ (τ j).cycleRange.symm x) hk
  exact congrArg Fin.val (by simpa [e, Function.comp] using hk' :
    τ (j.succAbove k) = (τ j).succAbove (deleted_index_perm τ j k))

/-- Helper for Definition 20.23.1: the deleted-index permutation carries exactly the sign
correction needed when the `j`-th differential summand is reindexed to the `τ j`-th summand. -/
theorem deleted_index_perm_coefficient {p : ℕ} (τ : Equiv.Perm (Fin (p + 2)))
    (j : Fin (p + 2)) :
    ((-1 : ℤ) ^ (j : ℕ)) * Equiv.Perm.sign (deleted_index_perm τ j) =
      Equiv.Perm.sign τ * ((-1 : ℤ) ^ (τ j : ℕ)) := by
  let e : Equiv.Perm (Fin (p + 2)) := (τ j).cycleRange * τ * j.cycleRange.symm
  have hdecomp : Equiv.Perm.decomposeFin e = (0, deleted_index_perm τ j) := by
    ext <;> simp [deleted_index_perm, e, Equiv.Perm.decomposeFin]
  have he :
      Equiv.Perm.decomposeFin.symm (0, deleted_index_perm τ j) = e := by
    apply (Equiv.Perm.decomposeFin).injective
    simpa using hdecomp.symm
  have hsign :
      Equiv.Perm.sign (deleted_index_perm τ j) = Equiv.Perm.sign e := by
    calc
      Equiv.Perm.sign (deleted_index_perm τ j) =
          Equiv.Perm.sign (Equiv.Perm.decomposeFin.symm (0, deleted_index_perm τ j)) := by
            rw [Equiv.Perm.decomposeFin.symm_sign]
            simp
      _ = Equiv.Perm.sign e := by
            rw [he]
  have hsign_e :
      Equiv.Perm.sign e =
        ((-1 : ℤ) ^ (τ j : ℕ)) * (Equiv.Perm.sign τ * ((-1 : ℤ) ^ (j : ℕ))) := by
    simp [e, Equiv.Perm.sign_mul, mul_assoc]
  have hpow : ((-1 : ℤ) ^ (j : ℕ)) * ((-1 : ℤ) ^ (j : ℕ)) = 1 := by
    rw [← pow_add]
    have htwo : (j : ℕ) + j = 2 * (j : ℕ) := by omega
    rw [htwo]
    simp
  calc
    ((-1 : ℤ) ^ (j : ℕ)) * Equiv.Perm.sign (deleted_index_perm τ j) =
        ((-1 : ℤ) ^ (j : ℕ)) * Equiv.Perm.sign e := by
          rw [hsign]
    _ = ((-1 : ℤ) ^ (j : ℕ)) *
          (((-1 : ℤ) ^ (τ j : ℕ)) * (Equiv.Perm.sign τ * ((-1 : ℤ) ^ (j : ℕ)))) := by
            rw [hsign_e]
    _ = Equiv.Perm.sign τ * ((-1 : ℤ) ^ (τ j : ℕ)) := by
          calc
            ((-1 : ℤ) ^ (j : ℕ)) *
                (((-1 : ℤ) ^ (τ j : ℕ)) * (Equiv.Perm.sign τ * ((-1 : ℤ) ^ (j : ℕ)))) =
              Equiv.Perm.sign τ * ((-1 : ℤ) ^ (τ j : ℕ)) *
                (((-1 : ℤ) ^ (j : ℕ)) * ((-1 : ℤ) ^ (j : ℕ))) := by
                  ring_nf
            _ = Equiv.Perm.sign τ * ((-1 : ℤ) ^ (τ j : ℕ)) * 1 := by rw [hpow]
            _ = Equiv.Perm.sign τ * ((-1 : ℤ) ^ (τ j : ℕ)) := by ring
