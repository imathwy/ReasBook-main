import Mathlib.RingTheory.Artinian.Module
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.

universe u

section

variable (R : Type u) [CommRing R]

/-
Definition 10.53.1 is recalled canonically by `IsArtinianRing R`: a commutative ring is Artinian
when it satisfies the descending chain condition for ideals.
-/
recall IsArtinianRing

/-- The textbook descending-chain formulation of an Artinian ring, stated directly for ideals. -/
theorem isArtinianRing_iff_ideal_descending_chain_condition :
    IsArtinianRing R ↔ ∀ (f : ℕ →o (Ideal R)ᵒᵈ),
      ∃ n : ℕ, ∀ m : ℕ, n ≤ m → f n = f m := by
  simpa [IsArtinianRing] using
    (show (∀ f : ℕ →o (Ideal R)ᵒᵈ, ∃ n : ℕ, ∀ m : ℕ, n ≤ m → f n = f m) ↔ IsArtinian R R from
      monotone_stabilizes_iff_artinian).symm

end
