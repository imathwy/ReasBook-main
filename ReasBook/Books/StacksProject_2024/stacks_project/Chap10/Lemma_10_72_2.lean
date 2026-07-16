import Mathlib
import StacksProject_2024.stacks_project.Chap10.Definition_10_72_1
import StacksProject_2024.stacks_project.Chap10.Lemma_10_20_1_Nakayama_s_lemma

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

/-- In a Noetherian local ring, the source-style condition that `I` is the unit ideal or contains
a regular sequence of length `n` is equivalent to the owner depth inequality `n ≤ I.depth R`. -/
theorem eq_top_or_exists_regularSequence_of_length_iff_le_depth (I : Ideal R) (n : ℕ) :
    (I = ⊤ ∨ ∃ rs : List R, IsRegular R rs ∧ ofList rs ≤ I ∧ rs.length = n) ↔
      (n : WithTop ℕ) ≤ I.depth R := sorry

end Ideal

end
