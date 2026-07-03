import Mathlib
import Mathlib.Algebra.Algebra.Operations
import StacksProject_2024.Chap10.Lemma_10_96_7

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

section

open scoped BigOperators

variable {R : Type u} [CommRing R]
variable {M : Type v} [AddCommGroup M] [Module R M]

private theorem isPrecomplete_span_singleton_of_mem
    {J : Ideal R} {f : R} (hfj : f ∈ J) (hM : IsAdicComplete J M) :
    IsPrecomplete (Ideal.span ({f} : Set R)) M := by
  classical
  let I : Ideal R := Ideal.span ({f} : Set R)
  let _ : IsAdicComplete J M := hM
  have smul_top_mono {A B : Ideal R} (hAB : A ≤ B) :
      A • (⊤ : Submodule R M) ≤ B • (⊤ : Submodule R M) := by
    intro y hy
    exact Submodule.smul_induction_on hy
      (fun r hr m hm ↦ Submodule.smul_mem_smul (hAB hr) hm)
      (fun x y hx hy ↦ by simpa using Submodule.add_mem _ hx hy)
  refine ⟨fun x hx ↦ ?_⟩
  have hstep : ∀ n, x n ≡ x (n + 1) [SMOD (I ^ n • (⊤ : Submodule R M))] := fun n ↦
    hx (Nat.le_succ n)
  have hexpansion : ∀ n, ∃ a : M, x (n + 1) - x n = f ^ n • a := by
    intro n
    have hxmem : x (n + 1) - x n ∈ I ^ n • (⊤ : Submodule R M) := by
      have hxmem' : x n - x (n + 1) ∈ I ^ n • (⊤ : Submodule R M) :=
        SModEq.sub_mem.mp (hstep n)
      simpa using Submodule.neg_mem _ hxmem'
    rw [show I ^ n = Ideal.span ({f ^ n} : Set R) by
      rw [show I = Ideal.span ({f} : Set R) by rfl, Ideal.span_singleton_pow]] at hxmem
    refine Submodule.smul_induction_on hxmem
      (fun r hr m _ ↦ ?_) (fun y z hy hz ↦ ?_)
    · rcases Ideal.mem_span_singleton.mp hr with ⟨s, hs⟩
      refine ⟨s • m, ?_⟩
      calc
        r • m = (f ^ n * s) • m := by rw [hs]
        _ = f ^ n • (s • m) := by rw [smul_smul]
    · rcases hy with ⟨y', hy'⟩
      rcases hz with ⟨z', hz'⟩
      exact ⟨y' + z', by rw [smul_add, hy', hz']⟩
  choose a ha using hexpansion
  let tails : ℕ → ℕ → M := fun n ↦ fun m ↦
    Finset.sum (Finset.range m) (fun k ↦ f ^ k • a (n + k))
  have htails_cauchy : ∀ n : ℕ,
      ∀ m, tails n m ≡ tails n (m + 1) [SMOD (J ^ m • (⊤ : Submodule R M))] := by
    intro n m
    rw [SModEq.sub_mem]
    have hm : f ^ m • a (n + m) ∈ J ^ m • (⊤ : Submodule R M) := by
      refine Submodule.smul_mem_smul ?_ Submodule.mem_top
      simpa using Ideal.pow_mem_pow hfj m
    have htaildiff : tails n m + -tails n (m + 1) = -(f ^ m • a (n + m)) := by
      simp [tails, Finset.sum_range_succ, add_comm, add_left_comm]
    rw [sub_eq_add_neg, htaildiff]
    exact Submodule.neg_mem _ hm
  have htails_full : ∀ n : ℕ, ∀ {m k}, m ≤ k →
      tails n m ≡ tails n k [SMOD (J ^ m • (⊤ : Submodule R M))] := by
    intro n m k hmk
    induction k, hmk using Nat.le_induction with
    | base => rfl
    | succ k hmk ih =>
        have hsub : J ^ k • (⊤ : Submodule R M) ≤ J ^ m • (⊤ : Submodule R M) :=
          smul_top_mono (Ideal.pow_le_pow_right hmk)
        exact ih.trans <|
          SModEq.mono hsub (htails_cauchy n k)
  have htails_limit : ∀ n : ℕ, ∃ b : M, ∀ m, tails n m ≡ b [SMOD (J ^ m • (⊤ : Submodule R M))] := by
    intro n
    exact hM.toIsPrecomplete.prec (htails_full n)
  choose b hb using htails_limit
  have hshift : ∀ n m, tails n (m + 1) = a n + f • tails (n + 1) m := by
    intro n m
    induction m with
    | zero =>
        simp [tails]
    | succ m ih =>
        simp [tails, Finset.sum_range_succ, ih, pow_succ, smul_add, smul_smul, mul_comm,
          add_comm, add_left_comm]
  have hb_rec : ∀ n, b n = a n + f • b (n + 1) := by
    intro n
    rw [← sub_eq_zero]
    apply hM.toIsHausdorff.haus
    intro m
    have hsub : J ^ (m + 1) • (⊤ : Submodule R M) ≤ J ^ m • (⊤ : Submodule R M) :=
      smul_top_mono (Ideal.pow_le_pow_right (Nat.le_succ m))
    have hleft : tails n (m + 1) ≡ b n [SMOD (J ^ m • (⊤ : Submodule R M))] := by
      exact SModEq.mono hsub (hb n (m + 1))
    have hright : tails n (m + 1) ≡ a n + f • b (n + 1) [SMOD (J ^ m • (⊤ : Submodule R M))] := by
      rw [hshift n m]
      exact SModEq.add SModEq.rfl (SModEq.smul (hb (n + 1) m) f)
    exact (sub_smodEq_zero).2 (hleft.symm.trans hright)
  let L := x 0 + b 0
  refine ⟨L, fun n ↦ ?_⟩
  have hL : ∀ n, L = x n + f ^ n • b n := by
    intro n
    induction n with
    | zero =>
        simp [L]
    | succ n ihn =>
        rw [ihn, hb_rec n, pow_succ, smul_add, smul_smul]
        have hxsucc : x n + f ^ n • a n = x (n + 1) := by
          simpa [add_comm, add_left_comm, add_assoc] using
            (sub_eq_iff_eq_add.1 (ha n)).symm
        simpa [add_assoc] using congrArg (fun t ↦ t + (f ^ n * f) • b (n + 1)) hxsucc
  rw [SModEq.sub_mem]
  rw [hL n]
  have hbmem : f ^ n • b n ∈ I ^ n • (⊤ : Submodule R M) := by
    rw [show I ^ n = Ideal.span ({f ^ n} : Set R) by
      rw [show I = Ideal.span ({f} : Set R) by rfl, Ideal.span_singleton_pow]]
    exact Submodule.smul_mem_smul (Ideal.mem_span_singleton_self _) Submodule.mem_top
  simpa [L, sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using Submodule.neg_mem _ hbmem

-- Proof sketch: use `IsAdicComplete J M` to get Hausdorffness for the weaker `I`-adic filtration
-- via `I ≤ J`. For precompleteness, first reduce from a finitely generated ideal to the principal
-- generator case using Lemma 10.96.7, then show a compatible `I`-adic Cauchy sequence is also
-- `J`-adically Cauchy and use `J`-adic completeness to produce the limit.
/-- Lemma 10.96.8: if `I ≤ J`, the ideal `I` is finitely generated, and `M` is `J`-adically
complete, then `M` is `I`-adically complete. -/
theorem isAdicComplete_of_le_of_fg
    {I J : Ideal R} (hIJ : I ≤ J) (hI : I.FG) (hM : IsAdicComplete J M) :
    IsAdicComplete I M := by
  refine { toIsHausdorff := ?_, toIsPrecomplete := ?_ }
  · let _ : IsHausdorff J M := hM.toIsHausdorff
    have hIJ' : Ideal.map (algebraMap R R) I ≤ J := by
      simpa using hIJ
    exact IsHausdorff.of_map hIJ'
  · rcases hI with ⟨s, hs⟩
    apply isPrecomplete_of_span_eq_of_generatorwise s hs
    intro f hf
    exact isPrecomplete_span_singleton_of_mem
      (show f ∈ J from hIJ <| hs ▸ Ideal.subset_span hf) hM

end
