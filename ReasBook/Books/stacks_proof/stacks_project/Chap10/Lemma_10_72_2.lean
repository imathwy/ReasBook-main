import Mathlib
import stacks_proof.stacks_project.Chap10.Definition_10_72_1
import stacks_proof.stacks_project.Chap10.Lemma_10_20_1_Nakayama_s_lemma

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

open RingTheory Sequence
open scoped ENat Pointwise

private lemma isWeaklyRegular_replicate_of_smul_eq_self {R : Type u} [CommRing R]
    {M : Type v} [AddCommGroup M] [Module R M] {f : R} (hf : ∀ m : M, f • m = m) :
    ∀ n : ℕ, IsWeaklyRegular M (List.replicate n f)
  | 0 => IsWeaklyRegular.nil R M
  | n + 1 => by
      refine IsWeaklyRegular.cons ?_ (isWeaklyRegular_replicate_of_smul_eq_self ?_ n)
      · intro x y hxy
        simpa [hf x, hf y] using hxy
      · intro q
        refine Quotient.inductionOn' q ?_
        intro x
        change (f • (Submodule.Quotient.mk x : QuotSMulTop f M)) = Submodule.Quotient.mk x
        rw [← Submodule.Quotient.mk_smul]
        exact congrArg Submodule.Quotient.mk (hf x)

namespace Ideal

variable {R : Type u} [CommRing R]
variable {M : Type v} [AddCommGroup M] [Module R M] [Module.Finite R M]

-- Proof sketch: split according to whether `IM = M`. In the nontrivial case, a weakly regular
-- sequence in `I` is automatically regular because `Ideal.ofList rs • ⊤ = ⊤` would force
-- `I • ⊤ = ⊤`. In the case `IM = M`, Nakayama produces `f ∈ I` acting as the identity on `M`,
-- so `List.replicate n f` is weakly regular for every `n`, forcing the supremum to be `∞`.
/-
Source/core/bridge triage:
* primary domain: commutative algebra, specifically depth and regular sequences;
* sampled owner API: `Ideal.depth`, `Ideal.regularSequenceLengths`,
  `RingTheory.Sequence.IsWeaklyRegular`,
  `Ideal.depth_eq_sSup_lengths_of_smul_top_ne_top`;
* layer: `source-facing`, since the textbook statement reformulates the owner notion `depth` using
  weakly regular sequences rather than introducing new primitive data;
* primitive vs derived split: the primitive data are the ideal `I`, the finite module `M`, and
  the owner predicates `IsRegular` / `IsWeaklyRegular`; the set of admissible lengths is derived
  API, so this proof compares the existing owner-side set `regularSequenceLengths I M` with the
  weakly-regular source-facing set instead of introducing a parallel public wrapper.
-/
/-- Lemma 10.72.2: for a finite `R`-module `M`, the depth of `M` with respect to `I` is the
supremum of the lengths of sequences `f₁, …, fᵣ` in `I` such that each `fᵢ` is a nonzerodivisor on
`M / (f₁, …, fᵢ₋₁)M`. -/
@[stacks 0AUI]
theorem depth_eq_sSup_lengths_of_isWeaklyRegular (I : Ideal R) (M : Type v)
    [AddCommGroup M] [Module R M] [Module.Finite R M] :
    I.depth M =
      sSup {d : ℕ∞ | ∃ rs : List R, IsWeaklyRegular M rs ∧ ofList rs ≤ I ∧ d = rs.length} := by
  let weaklyRegularSequenceLengths : Set ℕ∞ :=
    {d : ℕ∞ | ∃ rs : List R, IsWeaklyRegular M rs ∧ ofList rs ≤ I ∧ d = rs.length}
  change I.depth M = sSup weaklyRegularSequenceLengths
  by_cases hIM : I • (⊤ : Submodule R M) = ⊤
  · have hrange : Set.range (fun n : ℕ ↦ (n : ℕ∞)) ⊆ weaklyRegularSequenceLengths := by
      intro d hd
      rcases hd with ⟨n, rfl⟩
      obtain ⟨r, hrI, hr0⟩ :=
        exists_sub_one_mem_and_smul_eq_zero_of_ideal_smul_top_eq_top I hIM
      let f : R := 1 - r
      have hfI : f ∈ I := by
        dsimp [f]
        simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using I.neg_mem hrI
      have hf : ∀ m : M, f • m = m := by
        intro m
        dsimp [f]
        calc
          (1 - r) • m = (1 : R) • m - r • m := sub_smul _ _ _
          _ = m := by simpa using hr0 m
      dsimp [weaklyRegularSequenceLengths]
      refine ⟨List.replicate n f, isWeaklyRegular_replicate_of_smul_eq_self hf n, ?_, by simp⟩
      rw [span_le]
      intro a ha
      have hfa : a = f := (List.mem_replicate.mp ha).2
      simpa [hfa] using hfI
    rw [depth_eq_top_of_smul_top I M hIM]
    simpa [weaklyRegularSequenceLengths] using
      (top_unique <| calc
        (⊤ : ℕ∞) = sSup (Set.range fun n : ℕ ↦ (n : ℕ∞)) := by
          rw [sSup_range, ENat.iSup_natCast]
        _ ≤ sSup weaklyRegularSequenceLengths := by
          exact sSup_le_sSup hrange).symm
  · have hEq : I.regularSequenceLengths M = weaklyRegularSequenceLengths := by
      ext d
      dsimp [Ideal.regularSequenceLengths, weaklyRegularSequenceLengths]
      constructor
      · rintro ⟨rs, hreg, hmem, rfl⟩
        refine ⟨rs, hreg.toIsWeaklyRegular, ?_, rfl⟩
        change span {r | r ∈ rs} ≤ I
        rw [span_le]
        intro r hr
        exact hmem <| Ideal.subset_span hr
      · rintro ⟨rs, hweak, hle, rfl⟩
        refine ⟨rs, ⟨hweak, ?_⟩, hle, rfl⟩
        intro htop
        apply hIM
        exact top_unique <| htop.le.trans <|
          Submodule.smul_mono hle le_rfl
    simpa [weaklyRegularSequenceLengths] using
      (depth_eq_sSup_lengths_of_smul_top_ne_top I M hIM).trans (congrArg sSup hEq)

end Ideal

section

variable {R : Type u} [CommRing R] [IsLocalRing R] [IsNoetherianRing R]

namespace Ideal

omit [IsLocalRing R] [IsNoetherianRing R] in
/-- Helper for Chap10 Lemma 10 72 2: for the self-module `R`, the condition
`I • ⊤ = ⊤` is exactly `I = ⊤`. -/
private lemma ideal_smul_top_eq_top_iff_eq_top (I : Ideal R) :
    I • (⊤ : Submodule R R) = ⊤ ↔ I = ⊤ := by
  -- Rewrite the ideal action on the self-module as extension of scalars along `R →ₐ[R] R`.
  rw [Ideal.smul_top_eq_map]
  simp

omit [IsLocalRing R] [IsNoetherianRing R] in
/-- Helper for Chap10 Lemma 10 72 2: a proper ideal forces the ambient ring to be nontrivial. -/
private lemma nontrivial_of_ideal_ne_top {I : Ideal R} (hI : I ≠ ⊤) : Nontrivial R := by
  -- In a subsingleton ring all ideals coincide, contradicting properness of `I`.
  apply not_subsingleton_iff_nontrivial.mp
  intro hsub
  exact hI (Subsingleton.elim I ⊤)

omit [IsLocalRing R] [IsNoetherianRing R] in
/-- Helper for Chap10 Lemma 10 72 2: the ideal generated by the left side of an appended list
is contained in the ideal generated by the whole appended list. -/
private lemma ofList_append_left_le (rs ts : List R) :
    Ideal.ofList rs ≤ Ideal.ofList (rs ++ ts) := by
  -- It suffices to check the generators, since each left generator is a generator of the append.
  rw [span_le]
  intro x hx
  exact Ideal.subset_span (List.mem_append_left ts hx)

omit [IsLocalRing R] [IsNoetherianRing R] in
/-- Helper for Chap10 Lemma 10 72 2: the ideal generated by a prefix is contained in the ideal
generated by the original list. -/
private lemma ofList_take_le (rs : List R) (n : ℕ) :
    Ideal.ofList (rs.take n) ≤ Ideal.ofList rs := by
  -- View the original list as its prefix followed by its suffix.
  simpa [List.take_append_drop] using
    (ofList_append_left_le (R := R) (rs.take n) (rs.drop n))

omit [IsLocalRing R] [IsNoetherianRing R] in
/-- Helper for Chap10 Lemma 10 72 2: the left part of a regular appended sequence is regular. -/
private lemma isRegular_left_of_isRegular_append {M : Type v} [AddCommGroup M] [Module R M]
    {rs ts : List R} (hreg : IsRegular M (rs ++ ts)) : IsRegular M rs := by
  -- Weak regularity of the prefix is exactly the first projection of the append criterion.
  have hweak : IsWeaklyRegular M rs :=
    ((isWeaklyRegular_append_iff M rs ts).mp hreg.toIsWeaklyRegular).1
  refine ⟨hweak, ?_⟩
  intro htop
  -- If the prefix already generates the whole module, then the full list does too.
  have hle : Ideal.ofList rs • (⊤ : Submodule R M) ≤
      Ideal.ofList (rs ++ ts) • (⊤ : Submodule R M) :=
    Submodule.smul_mono (ofList_append_left_le rs ts) le_rfl
  have hfullTop : Ideal.ofList (rs ++ ts) • (⊤ : Submodule R M) = ⊤ := by
    exact top_unique <| calc
      ⊤ = Ideal.ofList rs • (⊤ : Submodule R M) := htop
      _ ≤ Ideal.ofList (rs ++ ts) • (⊤ : Submodule R M) := hle
  exact hreg.top_ne_smul hfullTop.symm

omit [IsLocalRing R] [IsNoetherianRing R] in
/-- Helper for Chap10 Lemma 10 72 2: every prefix of a regular sequence is regular. -/
private lemma isRegular_take {M : Type v} [AddCommGroup M] [Module R M]
    {rs : List R} (hreg : IsRegular M rs) (n : ℕ) : IsRegular M (rs.take n) := by
  -- Replace `rs` by `take n rs ++ drop n rs`, then take the left regular part.
  have happend : IsRegular M (rs.take n ++ rs.drop n) := by
    simpa [List.take_append_drop] using hreg
  exact isRegular_left_of_isRegular_append happend

omit [IsLocalRing R] [IsNoetherianRing R] in
/-- Helper for Chap10 Lemma 10 72 2: a finite lower bound for the supremum of regular sequence
lengths is witnessed by a regular sequence of at least that length. -/
private lemma exists_regularSequence_length_ge_of_natCast_le_sSup [Nontrivial R]
    {I : Ideal R} {n : ℕ} (h : (n : ℕ∞) ≤ sSup (I.regularSequenceLengths R)) :
    ∃ rs : List R, IsRegular R rs ∧ Ideal.ofList rs ≤ I ∧ n ≤ rs.length := by
  -- The zero bound is witnessed by the empty regular sequence.
  cases n with
  | zero =>
      have hreg : IsRegular R ([] : List R) := IsRegular.nil R R
      have hmem : Ideal.ofList ([] : List R) ≤ I := by
        simp
      have hlen : 0 ≤ ([] : List R).length := by
        simp
      exact ⟨[], hreg, hmem, hlen⟩
  | succ k =>
      -- For a positive bound, strictness below the supremum produces a longer witnessed length.
      have hkcast : (k : ℕ∞) < (k + 1 : ℕ∞) := by
        exact_mod_cast Nat.lt_succ_self k
      have hlt : (k : ℕ∞) < sSup (I.regularSequenceLengths R) :=
        lt_of_lt_of_le hkcast h
      rcases lt_sSup_iff.mp hlt with ⟨d, hd, hkd⟩
      rcases hd with ⟨rs, hreg, hmem, rfl⟩
      have hklt : k < rs.length := by
        exact_mod_cast hkd
      have hlen : k + 1 ≤ rs.length := Nat.succ_le_of_lt hklt
      exact ⟨rs, hreg, hmem, hlen⟩

/-- Chap10 Lemma 10 72 2: in a Noetherian local ring, the source-style condition that `I` is the
unit ideal or contains a regular sequence of length `n` is equivalent to the owner depth inequality
`n ≤ I.depth R`. -/
theorem eq_top_or_exists_regularSequence_of_length_iff_le_depth (I : Ideal R) (n : ℕ) :
    (I = ⊤ ∨ ∃ rs : List R, IsRegular R rs ∧ ofList rs ≤ I ∧ rs.length = n) ↔
      (n : WithTop ℕ) ≤ I.depth R := by
  -- Keep the local and Noetherian hypotheses attached to this source-facing formulation.
  let _ : IsLocalRing R := inferInstance
  let _ : IsNoetherianRing R := inferInstance
  constructor
  · intro h
    rcases h with htop | hseq
    · -- If `I` is the unit ideal, the depth branch is infinite.
      have hsmul : I • (⊤ : Submodule R R) = ⊤ :=
        (ideal_smul_top_eq_top_iff_eq_top I).2 htop
      rw [depth_eq_top_of_smul_top I R hsmul]
      exact le_top
    · rcases hseq with ⟨rs, hreg, hmem, hlen⟩
      -- Otherwise the given exact-length regular sequence is an element of `regularSequenceLengths`.
      by_cases hsmul : I • (⊤ : Submodule R R) = ⊤
      · rw [depth_eq_top_of_smul_top I R hsmul]
        exact le_top
      · rw [depth_eq_sSup_lengths_of_smul_top_ne_top I R hsmul]
        have hlenCast : (n : ℕ∞) = (rs.length : ℕ∞) := by
          exact_mod_cast hlen.symm
        have hmember : (n : ℕ∞) ∈ I.regularSequenceLengths R := by
          exact ⟨rs, hreg, hmem, hlenCast⟩
        exact le_sSup hmember
  · intro hdepth
    by_cases htop : I = ⊤
    · exact Or.inl htop
    · -- In the proper-ideal branch, rewrite depth as the supremum of regular sequence lengths.
      have hsmul : I • (⊤ : Submodule R R) ≠ ⊤ := by
        intro hsmul
        exact htop ((ideal_smul_top_eq_top_iff_eq_top I).1 hsmul)
      have hdepthSup : (n : ℕ∞) ≤ sSup (I.regularSequenceLengths R) := by
        simpa using hdepth.trans_eq (depth_eq_sSup_lengths_of_smul_top_ne_top I R hsmul)
      letI : Nontrivial R := nontrivial_of_ideal_ne_top htop
      rcases exists_regularSequence_length_ge_of_natCast_le_sSup (I := I) hdepthSup with
        ⟨rs, hreg, hmem, hlen⟩
      -- Truncate the long witness to get the requested exact length.
      have htakeReg : IsRegular R (rs.take n) := isRegular_take hreg n
      have htakeMem : Ideal.ofList (rs.take n) ≤ I :=
        (ofList_take_le rs n).trans hmem
      have htakeLen : (rs.take n).length = n := by
        rw [List.length_take, min_eq_left hlen]
      exact Or.inr ⟨rs.take n, htakeReg, htakeMem, htakeLen⟩

end Ideal

end
