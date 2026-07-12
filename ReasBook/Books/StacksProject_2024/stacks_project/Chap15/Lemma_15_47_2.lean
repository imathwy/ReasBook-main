import Mathlib
import StacksProject_2024.Chap05.Lemma_5_16_5
import StacksProject_2024.Chap15.Definition_15_47_1

-- Declarations for this item will be appended below by the statement pipeline.

universe u

open PrimeSpectrum
open scoped PrimeSpectrum

section

variable {R : Type u} [CommRing R]

variable [IsNoetherianRing R]

/- Domain-style sampling:
- primary domain: the Zariski topology on `PrimeSpectrum R`, the regular locus, and the chapter
  owners `IsJ0Ring`/`IsJ1Ring`;
- sampled owner declarations:
  `PrimeSpectrum.regularLocus`,
  `PrimeSpectrum.regularLocus_stableUnderGeneralization`,
  `isJ1Ring_iff_regularLocus_isOpen`,
  `PrimeSpectrum.pointsEquivIrreducibleCloseds`,
  `isOpen_iff_forall_irreducibleCloseds_inter_empty_or_contains_nonempty_open`;
- owner abstraction: the main statement should stay source-facing on `PrimeSpectrum R`, with
  `IsJ1Ring R` as the canonical owner and `V(p)` expressed by `zeroLocus p.asIdeal`;
- primitive vs. derived: the primitive data here is the existence of a nonempty open trace on the
  closed subset `V(p)`. The quotient-spectrum reformulation `IsJ0Ring (R ⧸ p.asIdeal)` is a
  bridge/view statement and should not replace the source-facing theorem.

Source/core/bridge triage:
- `source-facing`: the criterion on regular primes `p` and the closed subsets `V(p)`;
- `core/canonical`: `PrimeSpectrum.regularLocus`, `IsJ1Ring`, and the Noetherian openness
  criterion on irreducible closed subsets;
- `bridge/view`: `pointsEquivIrreducibleCloseds` identifies irreducible closed subsets with
  `zeroLocus p.asIdeal`, so the file should reuse that bridge instead of introducing a parallel
  wrapper around irreducible closed subsets.
-/

namespace PrimeSpectrum

-- Proof sketch: apply the Noetherian irreducible-closed openness criterion to `E`, identify each
-- irreducible closed subset of `Spec R` with `V(p)` via `PrimeSpectrum.pointsEquivIrreducibleCloseds`,
-- use the given hypothesis when `p ∈ E`, and use stability under generalization to obtain the
-- empty alternative when `p ∉ E`.
/-- For a subset `E` of `Spec R` that is stable under generalization, openness of `E` is
equivalent to the requirement that every point `p ∈ E` has a nonempty open trace on its closure
`V(p)` contained in `E`. -/
theorem isOpen_iff_forall_mem_zeroLocus_contains_nonempty_open_subset
    (E : Set (PrimeSpectrum R)) (hE_gen : StableUnderGeneralization E) :
    IsOpen E ↔
      ∀ p ∈ E,
        ∃ U : Set (PrimeSpectrum R), IsOpen U ∧ (U ∩ zeroLocus p.asIdeal).Nonempty ∧
          U ∩ zeroLocus p.asIdeal ⊆ E := by
  constructor
  · intro hE p hp
    refine ⟨E, hE, ?_, Set.inter_subset_left⟩
    exact ⟨p, hp, by simpa [mem_zeroLocus]⟩
  · intro h
    exact
      (isOpen_iff_forall_irreducibleCloseds_inter_empty_or_contains_nonempty_open E).2
        fun Y ↦ by
          let p := (PrimeSpectrum.pointsEquivIrreducibleCloseds R).symm Y
          have hY : (Y : Set (PrimeSpectrum R)) = zeroLocus p.asIdeal := by
            calc
              (Y : Set (PrimeSpectrum R)) =
                  ((show TopologicalSpace.IrreducibleCloseds (PrimeSpectrum R) from
                    PrimeSpectrum.pointsEquivIrreducibleCloseds R p :
                    TopologicalSpace.IrreducibleCloseds (PrimeSpectrum R)) :
                    Set (PrimeSpectrum R)) := by
                      simpa [p] using
                        congrArg
                          (fun Z : TopologicalSpace.IrreducibleCloseds (PrimeSpectrum R) ↦
                            (Z : Set (PrimeSpectrum R)))
                          ((PrimeSpectrum.pointsEquivIrreducibleCloseds R).apply_symm_apply Y).symm
              _ = zeroLocus p.asIdeal := by
                change closure ({p} : Set (PrimeSpectrum R)) = zeroLocus p.asIdeal
                simpa using closure_singleton p
          by_cases hp : p ∈ E
          · rcases h p hp with ⟨U, hU_open, hU_nonempty, hU_subset⟩
            right
            refine ⟨⟨Subtype.val ⁻¹' U, hU_open.preimage continuous_subtype_val⟩, ?_, ?_⟩
            · rcases hU_nonempty with ⟨x, hx⟩
              refine ⟨⟨x, ?_⟩, hx.1⟩
              change x ∈ (Y : Set (PrimeSpectrum R))
              rw [hY]
              exact hx.2
            · intro x hx
              have hxY : (x : PrimeSpectrum R) ∈ zeroLocus p.asIdeal := by
                rw [← hY]
                exact x.2
              exact hU_subset ⟨hx, hxY⟩
          · left
            ext x
            constructor
            · intro hx
              have hp_specializes_x : p ⤳ (x : PrimeSpectrum R) := by
                rw [← le_iff_specializes]
                simpa [hY, mem_zeroLocus] using x.2
              exact (hp <| hE_gen hp_specializes_x (by simpa using hx)).elim
            · intro hx
              simpa using hx

end PrimeSpectrum

-- Proof sketch: if the regular locus is open, take `U = Reg(Spec R)`. Conversely, apply the
-- Noetherian irreducible-closed openness criterion to `Reg(Spec R)`, identify each irreducible
-- closed subset of `Spec R` with `V(p)` via `PrimeSpectrum.pointsEquivIrreducibleCloseds`, use the
-- given hypothesis when `p` is regular, and use stability of the regular locus under
-- generalization to obtain the empty alternative when `p` is not regular.
/-- Lemma 15.47.2: for a Noetherian ring `R`, the ring is `J-1` if and only if for every regular
prime `p` of `Spec(R)`, the intersection `V(p) ∩ Reg(Spec(R))` contains a nonempty open subset of
`V(p)`, written as `U ∩ V(p)` for some open subset `U ⊆ Spec(R)`. -/
theorem isJ1Ring_iff_forall_regularPoint_zeroLocus_contains_nonempty_open_regular_subset :
    IsJ1Ring R ↔
      ∀ p ∈ Reg(Spec R),
        ∃ U : Set (PrimeSpectrum R), IsOpen U ∧ (U ∩ zeroLocus p.asIdeal).Nonempty ∧
          U ∩ zeroLocus p.asIdeal ⊆ Reg(Spec R) := by
  rw [isJ1Ring_iff_regularLocus_isOpen]
  exact
    isOpen_iff_forall_mem_zeroLocus_contains_nonempty_open_subset
      (Reg(Spec R)) (regularLocus_stableUnderGeneralization R)

end
