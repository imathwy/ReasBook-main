import Mathlib

universe u

/-- A finite group is `p`-solvable of height `h` if it is built recursively from `h` successive
normal extensions whose kernels have either order prime to `p` or `p`-power order. -/
def IsPSolvableOfHeight (p : ℕ) (h : ℕ) (G : Type u) [Group G] [Finite G] : Prop :=
  match h with
  | 0 => Subsingleton G
  | h + 1 =>
      ∃ I : Subgroup G,
        ∃ _ : I.Normal,
          (Nat.Coprime p (Nat.card I) ∨ IsPGroup p I) ∧
            IsPSolvableOfHeight p h (G ⧸ I)

/-- A finite group is `p`-solvable if it is `p`-solvable of some finite height. This is the
public owner predicate; the height-indexed family remains the recursive source-facing companion. -/
def IsPSolvable (p : ℕ) (G : Type u) [Group G] [Finite G] : Prop :=
  ∃ h : ℕ, IsPSolvableOfHeight p h G

section

variable {p : ℕ}
variable {h : ℕ}
variable {G : Type u} [Group G] [Finite G]

namespace IsPSolvableOfHeight

/-- Unfolding positive `p`-solvable height exhibits a normal subgroup whose order is either prime
to `p` or a `p`-power, with quotient of one smaller height. -/
theorem succ_iff :
    IsPSolvableOfHeight p (h + 1) G ↔
      ∃ I : Subgroup G,
        ∃ _ : I.Normal,
          (Nat.Coprime p (Nat.card I) ∨ IsPGroup p I) ∧
            IsPSolvableOfHeight p h (G ⧸ I) :=
  Iff.rfl

/-- `p`-solvable height is invariant under group isomorphism. -/
theorem of_equiv {H : Type*} [Group H] [Finite H] (e : G ≃* H)
    (hG : IsPSolvableOfHeight p h G) : IsPSolvableOfHeight p h H := by
  induction h generalizing G H with
  | zero =>
      letI : Subsingleton G := hG
      exact e.symm.injective.subsingleton
  | succ h ih =>
      obtain ⟨I, hI, hprop, hquot⟩ := hG
      let J : Subgroup H := I.map e.toMonoidHom
      have hJ : J.Normal := hI.map e.toMonoidHom e.surjective
      refine ⟨J, hJ, ?_, ?_⟩
      · rcases hprop with hcop | hP
        · left
          have hcard : Nat.card J = Nat.card I :=
            (Nat.card_congr (Subgroup.equivMapOfInjective I e.toMonoidHom e.injective).toEquiv).symm
          exact hcard ▸ hcop
        · right
          exact hP.of_equiv (Subgroup.equivMapOfInjective I e.toMonoidHom e.injective)
      · exact ih (G := G ⧸ I) (H := H ⧸ J) (QuotientGroup.congr I J e (by simp [J])) hquot

end IsPSolvableOfHeight

namespace IsPSolvable

/-- `p`-solvability is invariant under group isomorphism. -/
theorem of_equiv {H : Type*} [Group H] [Finite H] (e : G ≃* H) (hG : IsPSolvable p G) :
    IsPSolvable p H := by
  rcases hG with ⟨h, hh⟩
  exact ⟨h, hh.of_equiv e⟩

end IsPSolvable

end
