import LinearRepresentations_Serre_1977.Chap03.Theorem_3_3_2_1
import LinearRepresentations_Serre_1977.Chap04.Theorem_4_15

noncomputable section

open scoped Representation

universe u v w w'

namespace Representation

section

variable {G : Type u} [Group G] [TopologicalSpace G] [CompactSpace G]
  [MeasurableSpace G] [BorelSpace G] [IsTopologicalGroup G]
variable {V : Type v} [AddCommGroup V] [Module ℂ V] [TopologicalSpace V]
  [IsTopologicalAddGroup V] [ContinuousSMul ℂ V] [T2Space V] [FiniteDimensional ℂ V]
variable {W : Type w} [AddCommGroup W] [Module ℂ W] [TopologicalSpace W]
  [IsTopologicalAddGroup W] [ContinuousSMul ℂ W] [T2Space W] [FiniteDimensional ℂ W]
variable {ι : Type w'} [Finite ι]
local instance instDecidableEqTheorem_4_16Index : DecidableEq ι := Classical.decEq ι

/- Source/core/bridge triage:
- `source-facing`: Theorem 4-16 identifies the multiplicity of an irreducible summand `π` in an
  internal irreducible decomposition of `ρ` with the compact-group character pairing
  `(characterL2 ρ | characterL2 π)_G`.
- `core/canonical`: the multiplicity owner already present in the repository is
  `Representation.card_isomorphic_irreducible_summands_eq_finrank_intertwiningMap`.
- `bridge/view`: the compact-group pairing is the Chapter 4 bridge from that canonical
  intertwining-space dimension to the source-facing character formula.
-/

omit [TopologicalSpace G] [CompactSpace G] [MeasurableSpace G] [BorelSpace G]
  [IsTopologicalGroup G] [TopologicalSpace V] [IsTopologicalAddGroup V]
  [ContinuousSMul ℂ V] [T2Space V] [TopologicalSpace W] [IsTopologicalAddGroup W]
  [ContinuousSMul ℂ W] [T2Space W] in
/-- Helper for Theorem 4-16: the canonical multiplicity owner theorem from Chapter 3, cast from
`ℕ` to `ℂ` to match the compact-group character pairing. -/
private theorem nat_cast_card_isomorphic_irreducible_summands_eq_finrank_intertwiningMap
    (ρ : Representation ℂ G V)
    (σ : ι → Subrepresentation ρ)
    (hinternal : DirectSum.IsInternal (fun i ↦ (σ i).toSubmodule))
    (hσ : ∀ i, (σ i).toRepresentation.IsIrreducible)
    (π : Representation ℂ G W) [Representation.IsIrreducible π] :
    (Nat.card { i // Nonempty ((σ i).toRepresentation.Equiv π) } : ℂ) =
      Module.finrank ℂ (ρ.IntertwiningMap π) := by
  simpa using
    congrArg (fun n : ℕ ↦ (n : ℂ))
      (card_isomorphic_irreducible_summands_eq_finrank_intertwiningMap
        ρ σ hinternal hσ π inferInstance)

omit [TopologicalSpace G] [CompactSpace G] [MeasurableSpace G] [BorelSpace G]
  [IsTopologicalGroup G] [TopologicalSpace V] [IsTopologicalAddGroup V]
  [ContinuousSMul ℂ V] [T2Space V] [TopologicalSpace W] [IsTopologicalAddGroup W]
  [ContinuousSMul ℂ W] [T2Space W] in
/-- Helper for Theorem 4-16: the multiplicity count equals the finite indicator sum over those
summands whose attached irreducible representation is equivalent to `π`. -/
private theorem card_isomorphicIrreducibleSummands_cast_eq_sum_ite
    (ρ : Representation ℂ G V)
    (σ : ι → Subrepresentation ρ)
    (π : Representation ℂ G W) :
    by
      classical
      exact
        (Nat.card { i // Nonempty ((σ i).toRepresentation.Equiv π) } : ℂ) =
          ∑ i, if Nonempty ((σ i).toRepresentation.Equiv π) then (1 : ℂ) else 0 := by
  classical
  letI : Fintype ι := Fintype.ofFinite ι
  have hcount :
      Nat.card { i // Nonempty ((σ i).toRepresentation.Equiv π) } =
        ∑ i, if Nonempty ((σ i).toRepresentation.Equiv π) then 1 else 0 := by
    -- Rewrite the subtype cardinality as the cardinality of a filtered `Finset.univ`.
    rw [Nat.card_eq_fintype_card,
      Fintype.card_of_subtype
        (Finset.univ.filter fun i ↦ Nonempty ((σ i).toRepresentation.Equiv π))]
    · rw [Finset.card_filter]
    · intro i
      simp
  -- Cast the finite counting identity to `ℂ` so it matches the pairing surface.
  simpa using congrArg (fun n : ℕ ↦ (n : ℂ)) hcount

/-- Helper for Theorem 4-16: each subrepresentation of a continuous representation inherits the
continuity needed to form its `L²(G)` character. -/
private theorem subrepresentation_toRepresentation_isContinuous
    (ρ : Representation ℂ G V) [Representation.IsContinuous ρ]
    (σ : Subrepresentation ρ) :
    Representation.IsContinuous σ.toRepresentation := by
  refine Representation.isContinuous_of_continuousAction σ.toRepresentation ?_
  -- Check continuity after composing with the subtype inclusion into the ambient carrier.
  exact
    ((Representation.continuousAction ρ).comp
      (continuous_fst.prodMk (continuous_subtype_val.comp continuous_snd))).subtype_mk
      (fun gx ↦ σ.apply_mem_toSubmodule gx.1 gx.2.2)

/-- Helper for Theorem 4-16: the character of an internal direct sum is the sum of the characters
of the irreducible summands. -/
private theorem character_eq_sum_of_isInternal
    (ρ : Representation ℂ G V)
    (σ : ι → Subrepresentation ρ)
    (hinternal : DirectSum.IsInternal (fun i ↦ (σ i).toSubmodule)) :
    ρ.character = ∑ i, ((σ i).toRepresentation).character := by
  classical
  letI : Fintype ι := Fintype.ofFinite ι
  ext g
  -- Decompose the trace of `ρ g` along the internal family of invariant submodules.
  simpa [Representation.character] using
    (LinearMap.trace_eq_sum_trace_restrict
      (R := ℂ) (M := V) (N := fun i ↦ (σ i).toSubmodule) hinternal
      (f := ρ g) (hf := fun i ↦ (σ i).apply_mem_toSubmodule g))

/-- Helper for Theorem 4-16: the `L²(G)` character of an internal direct sum is the sum of the
`L²(G)` characters of the irreducible summands. -/
private theorem characterL2_eq_sum_of_isInternal
    (ρ : Representation ℂ G V) [Representation.IsContinuous ρ]
    (σ : ι → Subrepresentation ρ)
    (hinternal : DirectSum.IsInternal (fun i ↦ (σ i).toSubmodule))
    (hσcont : ∀ i, Representation.IsContinuous ((σ i).toRepresentation)) :
    by
      let χσ := fun i ↦
        letI : Representation.IsContinuous ((σ i).toRepresentation) := hσcont i
        characterL2 ((σ i).toRepresentation)
      exact characterL2 ρ = ∑ i, χσ i := by
  classical
  letI : Fintype ι := Fintype.ofFinite ι
  let χσ := fun i ↦
    letI : Representation.IsContinuous ((σ i).toRepresentation) := hσcont i
    characterL2 ((σ i).toRepresentation)
  -- First compare the continuous characters, then map that equality through `ContinuousMap.toLp`.
  suffices
      hchar :
        ({ toFun := ρ.character
           continuous_toFun := continuous_character_of_isContinuousCompact (ρ := ρ) } :
            C(G, ℂ)) =
          ∑ i,
            ({ toFun := ((σ i).toRepresentation).character
               continuous_toFun := continuous_character_of_isContinuousCompact
                 (ρ := (σ i).toRepresentation) } : C(G, ℂ)) by
    simpa [χσ, Representation.characterL2] using
      congrArg (ContinuousMap.toLp (E := ℂ) (p := (2 : ENNReal)) (μ := μG) ℂ) hchar
  ext g
  -- The pointwise character identity is exactly the trace decomposition above.
  simp [character_eq_sum_of_isInternal (ρ := ρ) (σ := σ) (hinternal := hinternal)]

/-- Theorem 4-16: if a finite-dimensional continuous complex representation `ρ` of a compact
group decomposes as an internal direct sum of irreducible subrepresentations `σ i`, then for any
irreducible finite-dimensional continuous complex representation `π`, the number of summands
isomorphic to `π` is `(χρ | χπ)_G`, written in Lean as `(characterL2 ρ | characterL2 π)_G`. -/
theorem card_isomorphic_irreducible_summands_eq_characterPairing_of_isInternal
    (ρ : Representation ℂ G V) [Representation.IsContinuous ρ]
    (σ : ι → Subrepresentation ρ)
    (hinternal : DirectSum.IsInternal (fun i ↦ (σ i).toSubmodule))
    (hσ : ∀ i, (σ i).toRepresentation.IsIrreducible)
    (π : Representation ℂ G W) [Representation.IsContinuous π] [Representation.IsIrreducible π] :
    Nat.card { i // Nonempty ((σ i).toRepresentation.Equiv π) } =
      (characterL2 ρ | characterL2 π)_G := by
  classical
  letI : Fintype ι := Fintype.ofFinite ι
  have hσcont : ∀ i, Representation.IsContinuous ((σ i).toRepresentation) := by
    intro i
    -- Each subrepresentation inherits continuity from the ambient continuous representation.
    exact subrepresentation_toRepresentation_isContinuous (ρ := ρ) (σ := σ i)
  let χσ := fun i ↦
    letI : Representation.IsContinuous ((σ i).toRepresentation) := hσcont i
    characterL2 ((σ i).toRepresentation)
  calc
    (Nat.card { i // Nonempty ((σ i).toRepresentation.Equiv π) } : ℂ) =
        ∑ i, if Nonempty ((σ i).toRepresentation.Equiv π) then (1 : ℂ) else 0 := by
          -- Normalize the multiplicity count to the finite sum that orthogonality produces.
          simpa using
            card_isomorphicIrreducibleSummands_cast_eq_sum_ite (ρ := ρ) (σ := σ) (π := π)
    _ = ∑ i, (χσ i | characterL2 π)_G := by
          -- Theorem 4-15 collapses each irreducible summand pairing to the corresponding indicator.
          refine Finset.sum_congr rfl ?_
          intro i _
          letI : Representation.IsContinuous ((σ i).toRepresentation) := hσcont i
          letI : Representation.IsIrreducible ((σ i).toRepresentation) := hσ i
          symm
          simpa [χσ] using
            (Representation.characterPairing_eq_ite_of_isIrreducible_of_isContinuousCompact
              ((σ i).toRepresentation) π)
    _ = (∑ i, χσ i | characterL2 π)_G := by
          -- The Chapter 4 pairing is linear in its first argument.
          symm
          simpa [squareIntegrableFunctionInner_eq_inner] using
            (inner_sum (𝕜 := ℂ) (s := Finset.univ) (f := χσ) (x := characterL2 π))
    _ = (characterL2 ρ | characterL2 π)_G := by
          -- Replace the summed `L²` character by the total character of `ρ`.
          rw [← characterL2_eq_sum_of_isInternal
            (ρ := ρ) (σ := σ) (hinternal := hinternal) (hσcont := hσcont)]

/-- Companion canonical form of Theorem 4-16: the same compact-group character pairing equals the
dimension of the intertwining space `ρ.IntertwiningMap π`. -/
theorem characterPairing_eq_finrank_intertwiningMap_of_isInternal
    (ρ : Representation ℂ G V) [Representation.IsContinuous ρ]
    (σ : ι → Subrepresentation ρ)
    (hinternal : DirectSum.IsInternal (fun i ↦ (σ i).toSubmodule))
    (hσ : ∀ i, (σ i).toRepresentation.IsIrreducible)
    (π : Representation ℂ G W) [Representation.IsContinuous π] [Representation.IsIrreducible π] :
    (characterL2 ρ | characterL2 π)_G = Module.finrank ℂ (ρ.IntertwiningMap π) := by
  calc
    (characterL2 ρ | characterL2 π)_G =
        Nat.card { i // Nonempty ((σ i).toRepresentation.Equiv π) } := by
          symm
          exact
            card_isomorphic_irreducible_summands_eq_characterPairing_of_isInternal
              ρ σ hinternal hσ π
    _ = Module.finrank ℂ (ρ.IntertwiningMap π) := by
          exact
            nat_cast_card_isomorphic_irreducible_summands_eq_finrank_intertwiningMap
              ρ σ hinternal hσ π

end

end Representation
