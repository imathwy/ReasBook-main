import LinearRepresentations_Serre_1977.Chap17.Theorem_17_17_6_1.FinalInductionPackaging

universe u v x

namespace Representation

section

variable {p : ℕ}
variable {A : Type u} [CommRing A] [HenselianLocalRing A]
variable [CharP (IsLocalRing.ResidueField A) p]
variable {G : Type v} [Group G] [Finite G]
variable {V : Type x} [AddCommGroup V] [Module (IsLocalRing.ResidueField A) V]
variable [FiniteDimensional (IsLocalRing.ResidueField A) V]
variable [IsAlgClosed (IsLocalRing.ResidueField A)]

local notation "k" => IsLocalRing.ResidueField A

/-- Helper for Theorem 17-17.6-1: once a concrete `p`-solvable height witness is available, the
lifting statement is exactly the height-indexed theorem proved in the local support package. -/
lemma exists_residueFieldLift_of_isIrreducible_of_isPSolvable_of_exists_height
    (hp : Nat.Prime p) (hG : ∃ h, IsPSolvableOfHeight p h G) (ρ : Representation k G V)
    [ρ.IsIrreducible] :
    ∃ (P : Type (max u v x)) (_ : AddCommGroup P) (_ : Module A P)
      (_ : Module.Free A P) (_ : Module.Finite A P)
      (ρA : Representation A G P)
      (red : P →ₗ[A] V),
        IsResidueFieldLift ρ ρA red := by
  -- Unpack the abstract `p`-solvable witness into Serre's height-indexed induction theorem.
  rcases hG with ⟨h, hh⟩
  -- The remaining work is exactly the already packaged height-indexed lifting statement.
  exact exists_residueFieldLift_of_isIrreducible_of_isPSolvableOfHeight hp hh ρ

/-- Theorem 17-17.6-1: if `A` is henselian local and the finite group `G` is `p`-solvable, then
every finite-dimensional irreducible representation of `G` over a sufficiently large residue field
of `A` admits a free finitely generated lift. In this Lean formulation, the largeness input used
by Serre's Schur-lemma step is represented by `[IsAlgClosed k]`. Equivalently, every simple
finite-dimensional `k[G]`-module lifts to a free finitely generated `A[G]`-module in the split
residue-field case. -/
theorem exists_residueFieldLift_of_isIrreducible_of_isPSolvable
    (hp : Nat.Prime p) (hG : IsPSolvable p G) (ρ : Representation k G V) [ρ.IsIrreducible] :
    ∃ (P : Type (max u v x)) (_ : AddCommGroup P) (_ : Module A P)
      (_ : Module.Free A P) (_ : Module.Finite A P)
      (ρA : Representation A G P)
      (red : P →ₗ[A] V),
        IsResidueFieldLift ρ ρA red := by
  -- Reduce the unindexed `p`-solvable hypothesis to the height-indexed helper proved above.
  exact
    exists_residueFieldLift_of_isIrreducible_of_isPSolvable_of_exists_height
      (A := A) (p := p) (G := G) (V := V) hp hG ρ

end

end Representation
