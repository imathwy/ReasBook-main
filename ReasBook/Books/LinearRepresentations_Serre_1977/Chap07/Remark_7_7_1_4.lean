import LinearRepresentations_Serre_1977.Chap07.Proposition_7_7_1_3

-- Declarations for this item will be appended below by the statement pipeline.

universe u v w x

namespace Representation

namespace IsIrreducible

variable {k : Type u} [Field k]
variable {G : Type v} [Group G]
variable {V : Type w} [AddCommGroup V] [Module k V]
variable {I : Type x} [MulAction G I]

section PermutedInternalSummands

/-- Remark 7-7.1-4: for an irreducible representation written as an internal direct sum of
nonzero submodules `W i`, the pretransitivity conclusion only needs the independence and
permutation data; the spanning hypothesis is redundant. -/
-- Proof sketch: for any orbit `O ⊆ I`, the supremum of the summands `W i` with `i ∈ O` is stable
-- under `ρ` because the family is permuted by `G`. Irreducibility forces this orbit submodule to
-- be either `⊥` or `⊤`. The nonzero hypothesis rules out `⊥` for every nonempty orbit, so there
-- can be only one orbit.
theorem isPretransitive_of_permuted_internalSummands
    (ρ : Representation k G V) [ρ.IsIrreducible]
    (W : I → Submodule k V)
    (hindep : iSupIndep W)
    (hperm : ρ.PermutesSubmoduleFamily W)
    (hne : ∀ i, W i ≠ ⊥) :
    MulAction.IsPretransitive G I := by
  classical
  by_cases hI : Nonempty I
  · let orbitSubmodule : I → Submodule k V := fun i ↦ ⨆ j ∈ MulAction.orbit G i, W j
    have hstable : ∀ i g, (orbitSubmodule i).map (ρ g) ≤ orbitSubmodule i := by
      intro i g
      dsimp [orbitSubmodule]
      rw [Submodule.map_iSup, iSup_le_iff]
      intro j
      rw [Submodule.map_iSup, iSup_le_iff]
      intro hj
      have hgj : (W j).map (ρ g) = W (g • j) := hperm g j
      rw [hgj]
      exact le_iSup_of_le (g • j) <|
        le_iSup_of_le (MulAction.mem_orbit_of_mem_orbit g hj) le_rfl
    let U : I → Subrepresentation ρ := fun i ↦
      { toSubmodule := orbitSubmodule i
        apply_mem_toSubmodule := by
          intro g v hv
          exact hstable i g <| Submodule.mem_map.mpr ⟨v, hv, rfl⟩ }
    have hU_top : ∀ i, U i = ⊤ := by
      intro i
      have hWi_le : W i ≤ (U i).toSubmodule := by
        exact le_iSup_of_le i <| le_iSup_of_le (MulAction.mem_orbit_self i) le_rfl
      have hU_ne_bot : U i ≠ ⊥ := by
        intro hU_bot
        have hbot : (U i).toSubmodule = ⊥ := by
          simpa using congrArg Subrepresentation.toSubmodule hU_bot
        exact hne i <| le_bot_iff.mp <| hbot ▸ hWi_le
      exact (IsSimpleOrder.eq_bot_or_eq_top (U i)).resolve_left hU_ne_bot
    have horbit_eq_univ : ∀ i, MulAction.orbit G i = (Set.univ : Set I) := by
      intro i
      apply Set.eq_univ_of_forall
      intro j
      have horbitSubmodule_top : orbitSubmodule i = ⊤ := by
        simpa [U, orbitSubmodule] using congrArg Subrepresentation.toSubmodule (hU_top i)
      exact hindep.mem_of_biSup_eq_top (by simpa [orbitSubmodule] using horbitSubmodule_top) (hne j)
    rcases hI with ⟨i0⟩
    exact (MulAction.isPretransitive_iff_orbit_eq_univ i0).2 (horbit_eq_univ i0)
  · letI : IsEmpty I := not_nonempty_iff.mp hI
    infer_instance

/-- Under the hypotheses of Remark 7-7.1-4, Proposition 7-7.1-3 applies to any chosen summand:
`ρ` is induced from the stabilizer of `W i0` acting on that summand. -/
theorem isInducedFromStabilizer_of_permuted_internalSummands
    (ρ : Representation k G V) [ρ.IsIrreducible]
    (W : I → Submodule k V) (i0 : I)
    (hindep : iSupIndep W) (hspan : iSup W = ⊤)
    (hperm : ρ.PermutesSubmoduleFamily W)
    (hne : ∀ i, W i ≠ ⊥) :
    ρ.IsInducedFromSubrepresentation
      (ρ.submoduleStabilizer (W i0))
      (ρ.stabilizedSubrepresentation (W i0)) := by
  letI : MulAction.IsPretransitive G I :=
    isPretransitive_of_permuted_internalSummands ρ W hindep hperm hne
  simpa using
    isInducedFromSubrepresentation_submoduleStabilizer_of_indep_span_of_permuted_family
      ρ W i0 hindep hspan hperm

end PermutedInternalSummands

end IsIrreducible

end Representation
