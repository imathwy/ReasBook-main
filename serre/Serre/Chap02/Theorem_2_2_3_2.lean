import Serre.Chap02.CompleteIrreducibleFamily
import Serre.RepresentationTheory.GroupFunctionPairing

-- Declarations for this item will be appended below by the statement pipeline.

universe u v w u₁ u₂

namespace Representation

noncomputable section

open scoped Representation

section

variable {G : Type u} [Group G] [Finite G]
variable {K : Type u₁} [Field K] [IsAlgClosed K] [Invertible (Nat.card G : K)]
variable {V : Type v} [AddCommGroup V] [Module K V] [FiniteDimensional K V]
variable {W : Type w} [AddCommGroup W] [Module K W] [FiniteDimensional K W]
variable {ι : Type u₂} [Finite ι]

local instance : DecidableEq ι := Classical.decEq ι

/- Domain-style sampling for this item:
* primary domain: multiplicities of irreducible summands via intertwining spaces and character
  pairings in finite-dimensional representation theory;
* relevant owner declarations inspected before refining:
  `Representation.finrank_intertwiningMap_eq_ite_one_zero_of_isIrreducible`,
  `Representation.card_isomorphic_irreducible_summands_eq_finrank_intertwiningMap`,
  `Representation.groupFunctionPairingOverField_character_eq_finrank_intertwiningMap`;
* best owner abstraction: the multiplicity owner theorem
  `Representation.card_isomorphic_irreducible_summands_eq_finrank_intertwiningMap`, with the
  character-pairing theorem as the canonical bridge from intertwining-space dimension to the scalar
  product of characters.

Primitive data vs derived API:
* primitive data are the representation `ρ`, the internal irreducible decomposition `σ`, and the
  target irreducible representation `τ`;
* the nat-valued multiplicity theorem is already primitive chapter API upstream, so this file keeps
  only the derived field-valued cast-and-pairing consequence instead of re-declaring parallel local
  copies of the owner theorems.

Source/core/bridge triage:
* source-facing: the field-valued multiplicity formula of Theorem `2-2.3-2`;
* core/canonical: the upstream owner theorem
  `Representation.card_isomorphic_irreducible_summands_eq_finrank_intertwiningMap`;
* bridge/view: the scalar cast from `ℕ` to `K`, followed by the character-pairing identification
  of `Module.finrank K (ρ.IntertwiningMap τ)`. -/

omit [Finite G] [Invertible (Nat.card G : K)] in
/-- Helper for Theorem 2-2.3-2: casting the nat-valued multiplicity formula into `K` produces the
field-valued intertwining-dimension equality used in the character-pairing statement. -/
private theorem nat_cast_card_isomorphic_irreducible_summands_eq_finrank_intertwiningMap
    (ρ : Representation K G V) (σ : ι → Subrepresentation ρ)
    (hinternal : DirectSum.IsInternal (fun i ↦ (σ i).toSubmodule))
    (hσ : ∀ i, (σ i).toRepresentation.IsIrreducible)
    (τ : Representation K G W) [τ.IsIrreducible] :
    (Nat.card { i // Nonempty (((σ i).toRepresentation).Equiv τ) } : K) =
      Module.finrank K (ρ.IntertwiningMap τ) := by
  -- Cast the upstream nat-valued multiplicity identity into `K`.
  simpa using
    congrArg (fun n : ℕ ↦ (n : K))
      (card_isomorphic_irreducible_summands_eq_finrank_intertwiningMap
        ρ σ hinternal hσ τ inferInstance)

/-- Theorem 2-2.3-2: if a finite-dimensional `K`-representation `ρ` of a finite group is a direct
sum of irreducible subrepresentations `σ i`, where `K` is algebraically closed and `|G|` is
invertible in `K`, then the number of summands isomorphic to an irreducible representation `τ`
has image under the canonical scalar cast in `K` equal to the normalized scalar product of the
characters `ρ.character` and `τ.character`. -/
theorem card_isomorphic_irreducible_summands_cast_eq_character_pairing
    (ρ : Representation K G V) (σ : ι → Subrepresentation ρ)
    (hinternal : DirectSum.IsInternal (fun i ↦ (σ i).toSubmodule))
    (hσ : ∀ i, (σ i).toRepresentation.IsIrreducible)
    (τ : Representation K G W) [τ.IsIrreducible] :
    (Nat.card { i // Nonempty (((σ i).toRepresentation).Equiv τ) } : K) =
      ⟪ρ.character, τ.character⟫ := by
  -- First identify the multiplicity with the finrank of the intertwining space.
  calc
    (Nat.card { i // Nonempty (((σ i).toRepresentation).Equiv τ) } : K) =
        Module.finrank K (ρ.IntertwiningMap τ) := by
          exact
            nat_cast_card_isomorphic_irreducible_summands_eq_finrank_intertwiningMap
              ρ σ hinternal hσ τ
    -- Then rewrite the same invariant as the character pairing.
    _ = ⟪ρ.character, τ.character⟫ := by
          symm
          simpa using
            (Representation.groupFunctionPairingOverField_character_eq_finrank_intertwiningMap
              K ρ τ)

end

end

end Representation
