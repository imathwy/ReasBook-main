import LinearRepresentations_Serre_1977.Chap08.Proposition_8_8_3_7

-- Declarations for this item will be appended below by the statement pipeline.

universe u v w

section

open Representation

variable {p : ℕ}
variable {k : Type u} [Field k] [CharP k p] [Fact p.Prime]
variable {G : Type v} [Group G] [Finite G]
variable {V : Type w} [AddCommGroup V] [Module k V]
variable (ρ : Representation k G V) [ρ.IsIrreducible]

-- Proof sketch: Proposition `8-8.3-7` gives a nonzero invariant vector, so `ρ.invariants` is a
-- nonzero `G`-stable subspace. Irreducibility forces that invariant subspace to be all of `V`,
-- hence every group element acts as the identity and the representation is trivial.
/-- Corollary 8-8.3-8: an irreducible representation of a finite `p`-group over a field of
characteristic `p` is trivial. -/
theorem isTrivial_of_isIrreducible_of_isPGroup_charP (hG : IsPGroup p G) :
    ρ.IsTrivial := by
  let _ : Nontrivial V := by
    by_contra hV
    haveI : Subsingleton V := not_nontrivial_iff_subsingleton.mp hV
    exact (show (⊥ : Subrepresentation ρ) ≠ ⊤ from IsSimpleOrder.bot_ne_top) <| by
      apply Subrepresentation.toSubmodule_injective
      ext x
      constructor
      · intro _
        exact Submodule.mem_top
      · intro _
        simpa using (show x = 0 from Subsingleton.elim x 0)
  have h_invariants : ρ.invariants = ⊤ := by
    let U : Subrepresentation ρ :=
      { toSubmodule := ρ.invariants
        apply_mem_toSubmodule g := by
          intro x hx
          simpa [(ρ.mem_invariants x).mp hx g] using hx }
    have hU_toSubmodule_ne_bot : U.toSubmodule ≠ ⊥ := by
      simpa [U] using invariants_ne_bot_of_isPGroup_charP ρ hG
    have hU_ne_bot : U ≠ ⊥ := by
      intro hU
      exact hU_toSubmodule_ne_bot <| by
        simpa using congrArg Subrepresentation.toSubmodule hU
    have hU_top : U = ⊤ := (IsSimpleOrder.eq_bot_or_eq_top U).resolve_left hU_ne_bot
    simpa [U] using congrArg Subrepresentation.toSubmodule hU_top
  refine ⟨fun g ↦ ?_⟩
  ext x
  have hx : x ∈ ρ.invariants := by simp [h_invariants]
  exact (ρ.mem_invariants x).1 hx g

end
