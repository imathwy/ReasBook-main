import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

universe u v w

open Representation

section

variable {k : Type u} {G : Type v} {V : Type w}
variable [Field k] [Group G] [NeZero (Nat.card G : k)]
variable [AddCommGroup V] [Module k V]

/-- Theorem 1-1.3-1: every `G`-stable subspace of a representation over a field in which `|G|` is
invertible has a `G`-stable complementary subspace; in particular, this recovers the complex case
from the text. -/
-- Proof sketch: view the stable subspace `W` as a subrepresentation of `ρ`. Maschke's theorem
-- makes `ρ` semisimple, so this subrepresentation has a complementary subrepresentation; then
-- pass back to the underlying submodules.
theorem exists_isCompl_of_mem_invtSubmodule (ρ : Representation k G V) (W : Submodule k V)
    (hW : W ∈ ρ.invtSubmodule) :
    ∃ W₀ : ρ.invtSubmodule, IsCompl W (W₀ : Submodule k V) := by
  -- Maschke's theorem needs finiteness of `G`, which follows from `Nat.card G ≠ 0`.
  have hcard : Nat.card G ≠ 0 := by
    intro h
    exact NeZero.ne (Nat.card G : k) <| by simp [h]
  let _ : Finite G := Nat.finite_of_card_ne_zero hcard
  -- Repackage the stable subspace as a subrepresentation so that Maschke applies directly.
  let σ : Subrepresentation ρ :=
    { toSubmodule := W
      apply_mem_toSubmodule := by
        simpa [Representation.mem_invtSubmodule,
          Module.End.mem_invtSubmodule_iff_forall_mem_of_mem] using hW }
  obtain ⟨σ₀, hσ₀⟩ := exists_isCompl σ
  refine ⟨⟨σ₀.toSubmodule, ?_⟩, ?_⟩
  · simpa [Representation.mem_invtSubmodule,
      Module.End.mem_invtSubmodule_iff_forall_mem_of_mem] using σ₀.apply_mem_toSubmodule
  -- Transport the complement relation from subrepresentations back to submodules.
  · refine ⟨?_, ?_⟩
    · rw [disjoint_iff]
      have hdisj : σ ⊓ σ₀ = ⊥ := by
        simpa [disjoint_iff] using hσ₀.disjoint
      simpa [σ] using congrArg Subrepresentation.toSubmodule hdisj
    · rw [codisjoint_iff]
      have hcodisj : σ ⊔ σ₀ = ⊤ := by
        simpa [codisjoint_iff] using hσ₀.codisjoint
      simpa [σ] using congrArg Subrepresentation.toSubmodule hcodisj

end
