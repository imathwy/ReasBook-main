import stacks_proof.stacks_project.Chap10.Lemma_10_96_5.Index

-- Declarations for this item will be appended below by the statement pipeline.

universe u

noncomputable section

open AdicCompletion
open CategoryTheory
open CategoryTheory.Limits

variable {R : Type u} [CommRing R]
variable (I : Ideal R)
variable (M : Type u) [AddCommGroup M] [Module R M]

-- Domain-style sampling:
-- * source-facing layer: a criterion for when the completion `AdicCompletion I M` is itself
--   `I`-adically complete, phrased by the kernels of the canonical quotient maps.
-- * core/canonical owner: `IsAdicComplete I (AdicCompletion I M)` together with the kernel
--   description `AdicCompletion.pow_smul_top_eq_ker_eval`.
-- * relevant sampled declarations:
--   `IsAdicComplete`,
--   `AdicCompletion.of_bijective_iff`,
--   `AdicCompletion.isAdicComplete`,
--   `AdicCompletion.pow_smul_top_eq_ker_eval`.
-- * primitive data: the owner object `AdicCompletion I M`; the submodules `ker (eval I M n)` are
--   derived from its canonical projections.
-- * bridge/view output: the textbook iff re-expressed directly in terms of the owner completion
--   object and its canonical evaluation maps.
--
-- Proof sketch: let `K_n = (AdicCompletion.eval I M n).ker`. The short exact sequences
-- `0 → K_n / I^n M^∧ → M^∧ / I^n M^∧ → M / I^n M → 0` form an inverse system with surjective
-- transition maps on the left. Applying Lemma `10.87.1` to these systems identifies the adic
-- completion of `M^∧` with `M^∧` precisely when each quotient `K_n / I^n M^∧` vanishes, i.e. when
-- `K_n = I^n M^∧` for every positive `n`.
/-- Chap10 Lemma 10 96 5: the `I`-adic completion `AdicCompletion I M` is `I`-adically complete if and
only if, for every positive integer `n`, the kernel of the canonical projection
`AdicCompletion I M → M ⧸ (I ^ n • ⊤)` is exactly `I ^ n` times the completed module. -/
@[stacks 0318]
theorem isAdicComplete_adicCompletion_iff_ker_eval_eq_pow_smul_top :
    IsAdicComplete I (AdicCompletion I M) ↔
      ∀ n : ℕ+,
        (eval I M (n : ℕ)).ker =
          I ^ (n : ℕ) • (⊤ : Submodule R (AdicCompletion I M)) := by
  constructor
  · intro hcomplete
    have hleftZero :
        IsZero (limit (positive_stage_left_system (R := R) (I := I) (M := M))) := by
      -- Route correction: after the stagewise descent is installed, only the source-faithful
      -- inverse-limit exactness argument remains. The positive-stage comparison is rewritten as
      -- the completeness retraction `(M^∧)^∧ → M^∧`, so exactness and injectivity now finish.
      exact positive_stage_left_limit_isZero_of_complete
        (R := R) (I := I) (M := M) hcomplete
    intro n
    exact ker_eval_eq_pow_smul_top_of_left_limit_isZero
      (R := R) (I := I) (M := M) hleftZero n
  · intro hker
    refine
      { toIsHausdorff := ?_, toIsPrecomplete := ?_ }
    · -- The kernel description forces every element vanishing modulo all `I ^ n` to be zero.
      refine ⟨fun x hx ↦ ?_⟩
      ext n
      cases n with
      | zero =>
          have hs : Subsingleton (M ⧸ (I ^ 0 • (⊤ : Submodule R M))) := by
            simpa using (show Subsingleton (M ⧸ (⊤ : Submodule R M)) from inferInstance)
          exact @Subsingleton.elim _ hs _ _
      | succ n =>
          have hxmem :
              x ∈ I ^ (n + 1) • (⊤ : Submodule R (AdicCompletion I M)) := by
            exact SModEq.zero.1 (hx (n + 1))
          have hkerStage :
              (eval I M (n + 1)).ker =
                I ^ (n + 1) • (⊤ : Submodule R (AdicCompletion I M)) := by
            simpa using hker ⟨n + 1, Nat.succ_pos _⟩
          have hxker : x ∈ (eval I M (n + 1)).ker := by
            rw [hkerStage]
            exact hxmem
          exact LinearMap.mem_ker.mp hxker
    · -- Reuse the standard completion proof skeleton, replacing finite generation by `hker`.
      refine ⟨fun x hx ↦ ?_⟩
      let L : AdicCompletion I M := {
        val i := (x i).val i
        property {m n} hmn := by
          cases m with
          | zero =>
              have hs : Subsingleton (M ⧸ (I ^ 0 • (⊤ : Submodule R M))) := by
                simpa using (show Subsingleton (M ⧸ (⊤ : Submodule R M)) from inferInstance)
              exact @Subsingleton.elim _ hs _ _
          | succ m =>
              have hkerStage :
                  I ^ (m + 1) • (⊤ : Submodule R (AdicCompletion I M)) =
                    (eval I M (m + 1)).ker := by
                simpa using (hker ⟨m + 1, Nat.succ_pos _⟩).symm
              have hcompat : (x n).val (m + 1) = (x (m + 1)).val (m + 1) := by
                have hcompat' := hx hmn
                rwa [SModEq.sub_mem, hkerStage, LinearMap.mem_ker,
                  _root_.map_sub, sub_eq_zero, eval_apply, eval_apply, eq_comm] at hcompat'
              calc
                AdicCompletion.transitionMap I M hmn ((fun i ↦ (x i).val i) n)
                    = (x n).val (m + 1) := by
                        simpa using AdicCompletion.transitionMap_comp_eval_apply
                          (I := I) (M := M) (m := m + 1) (n := n) (hmn := hmn) (x := x n)
                _ = (x (m + 1)).val (m + 1) := hcompat
      }
      use L
      intro i
      cases i with
      | zero =>
          rw [SModEq.sub_mem]
          simpa using
            (show x 0 - L ∈ (⊤ : Submodule R (AdicCompletion I M)) from Submodule.mem_top _)
      | succ i =>
          -- At stage `i + 1`, the difference vanishes because its image in the quotient is zero.
          have hkerStage :
              I ^ (i + 1) • (⊤ : Submodule R (AdicCompletion I M)) =
                (eval I M (i + 1)).ker := by
            simpa using (hker ⟨i + 1, Nat.succ_pos _⟩).symm
          rw [SModEq.sub_mem, hkerStage, LinearMap.mem_ker,
            _root_.map_sub, sub_eq_zero, eval_apply]
          simp [L]

end
