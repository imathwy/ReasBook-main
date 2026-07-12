import Mathlib
import LinearRepresentations_Serre_1977.RepresentationTheory.RealizableOver
import LinearRepresentations_Serre_1977.Chap14.Remark_14_14_5_1.SemisimpleSchur
import LinearRepresentations_Serre_1977.Chap14.Remark_14_14_5_1.FieldIndependence.GeneralBaseChange

/-!
# Absolute irreducibility ascends along any extension of an algebraically closed base

Over an algebraically closed field `L` of characteristic `0`, every irreducible representation is
*absolutely* irreducible: its endomorphism ring is `L` (Schur), so after extending scalars to **any**
field extension `E ⊇ L` it stays irreducible. This is Brick 1 of the field-independence project.

Proof: `dim_L End_{L[G]}(ρ) = 1` (Schur over the algebraically closed `L`); the End base-change
equality `finrank_intertwiningMap_eq_baseChange` carries this to `dim_E End_{E[G]}(ρ ⊗ E) = 1`;
characteristic `0` makes `E[G]` semisimple (Maschke), and a semisimple representation with
one-dimensional self-intertwiners is irreducible (`SemisimpleSchur`).
-/

noncomputable section

universe u

open scoped TensorProduct

namespace Representation

variable {L : Type u} [Field L] [CharZero L] [IsAlgClosed L]
variable {E : Type u} [Field E] [Algebra L E]
variable {G : Type u} [Group G] [Finite G]
variable {W : Type u} [AddCommGroup W] [Module L W] [FiniteDimensional L W]

/-- **Brick 1 — absolute irreducibility ascends.** If `L` is an algebraically closed field of
characteristic `0` and `ρ` is an irreducible finite-dimensional `L`-representation of `G`, then its
scalar extension to any field extension `E ⊇ L` is again irreducible. -/
theorem isIrreducible_scalarExtension_of_isAlgClosed_base
    (ρ : Representation L G W) (hρ : ρ.IsIrreducible) :
    (Representation.scalarExtension (k := E) ρ).IsIrreducible := by
  -- Characteristic `0` passes to the extension `E` (along the injective `algebraMap L E`).
  haveI : CharZero E := ⟨fun {a b} h => by
    have h' : algebraMap L E (a : L) = algebraMap L E (b : L) := by
      rw [map_natCast, map_natCast]; exact h
    exact Nat.cast_injective ((algebraMap L E).injective h')⟩
  -- Schur over the algebraically closed base: `dim_L End(ρ) = 1`.
  have h1 : Module.finrank L (Representation.IntertwiningMap ρ ρ) = 1 :=
    hρ.finrank_intertwiningMap_self
  -- End base change carries it to `E`.
  have h2 : Module.finrank E
      (Representation.IntertwiningMap
        (Representation.scalarExtension (k := E) ρ) (Representation.scalarExtension (k := E) ρ)) = 1 := by
    rw [finrank_intertwiningMap_eq_baseChange ρ, h1]
  -- Characteristic `0` makes `|G|` invertible in `E`, so Maschke makes `ρ ⊗ E` semisimple.
  haveI : NeZero (Nat.card G : E) := ⟨Nat.cast_ne_zero.mpr Nat.card_pos.ne'⟩
  exact isIrreducible_of_isSemisimpleRepresentation_of_finrank_intertwiningMap_eq_one
    (Representation.scalarExtension (k := E) ρ) h2

end Representation
