import Mathlib
import StacksProject_2024.Chap10.Definition_10_59_1
import StacksProject_2024.Chap15.Definition_15_15_1

-- Declarations for this item will be appended below by the statement pipeline.

universe u

open Ideal IsLocalRing

section

variable {R : Type u} [CommRing R] [IsLocalRing R]

namespace Ideal

/- Domain triage:
* primary domain: local commutative algebra of associated and weakly associated ideals.
* sampled owner abstractions in the same domain:
  `Ideal.IsWeaklyAssociatedToModule`, `Ideal.IsIdealOfDefinition`, `Ideal.IsIdealOfDefinition.isPrimary`,
  `Ideal.exists_pow_le_of_le_radical_of_fg`, and
  `IsAutoAssociatedRing.exists_torsionOf_isIdealOfDefinition`.
* `core/canonical`: the owner APIs are `Ideal.torsionOf`, `Ideal.IsIdealOfDefinition`,
  `Ideal.exists_pow_le_of_le_radical_of_fg`, and the chapter witness theorem
  `IsAutoAssociatedRing.exists_torsionOf_isIdealOfDefinition`.
* `source-facing`: `IsAutoAssociatedRing.annihilator_ne_bot_of_fg_of_ne_top` is the chapter's
  property `(P)` for auto-associated rings.
* `bridge/view`: the theorem below passes from the owner witness `Ideal.torsionOf R R x` through
  the canonical predicate `Ideal.IsIdealOfDefinition` to the annihilator conclusion for a given
  proper finitely generated ideal.
-/

local notation "AnnR[" x "]" => torsionOf R R x

-- Proof sketch: take `x` whose torsion ideal is an ideal of definition. For a proper finitely
-- generated ideal `I`, some power `I^n` lies in `Ideal.torsionOf R R x`. Choose `n` minimal.
-- Then `n > 0`, and `I^(n - 1)` contains an element `a` with `a * x ≠ 0`; minimality forces
-- `I * (a * x) = 0`, so `a * x` is a nonzero element of `I.annihilator`.
theorem annihilator_ne_bot_of_fg_of_ne_top_of_torsionOf_isIdealOfDefinition
    (x : R) (hxdef : AnnR[x].IsIdealOfDefinition)
    {I : Ideal R} (hI : I.FG) (hproper : I ≠ ⊤) :
    I.annihilator ≠ ⊥ := by
  let J : Ideal R := AnnR[x]
  have hJ : J.IsIdealOfDefinition := by simpa [J] using hxdef
  have hIle : I ≤ J.radical := by
    calc
      I ≤ maximalIdeal R := IsLocalRing.le_maximalIdeal hproper
      _ = J.radical := by simpa [Ideal.IsIdealOfDefinition] using hJ.symm
  have hpow : ∃ n : ℕ, I ^ n ≤ J := exists_pow_le_of_le_radical_of_fg hIle hI
  classical
  let n := Nat.find hpow
  have hn : I ^ n ≤ J := Nat.find_spec hpow
  have hn_ne_zero : n ≠ 0 := by
    intro hn_zero
    exact hJ.isPrimary.ne_top <| top_le_iff.mp <| by simpa [n, hn_zero] using hn
  have hnot : ¬ I ^ (n - 1) ≤ J := by
    intro hle
    have hmin : n ≤ n - 1 := Nat.find_min' hpow <| by simpa [n] using hle
    omega
  rw [SetLike.not_le_iff_exists] at hnot
  rcases hnot with ⟨a, ha, hax⟩
  have hy : a * x ∈ I.annihilator := by
    rw [Submodule.mem_annihilator]
    intro b hb
    have hba : b * a ∈ I ^ n := by
      have hba' : b * a ∈ I ^ (n - 1) * I := by
        simpa [mul_comm] using Ideal.mul_mem_mul_rev ha hb
      have hn_eq : n = (n - 1) + 1 := by omega
      rw [hn_eq, pow_succ]
      exact hba'
    have hkill : (b * a) * x = 0 := by
      simpa [J, mem_torsionOf_iff] using hn hba
    simpa [mul_assoc, mul_comm, mul_left_comm] using hkill
  intro hann
  have hax_ne_zero : a * x ≠ 0 := by
    simpa [J, mem_torsionOf_iff] using hax
  have hzero : a * x = 0 := by
    have : a * x ∈ (⊥ : Ideal R) := by simpa [hann] using hy
    simpa [mem_bot] using this
  exact hax_ne_zero hzero

end Ideal

section

variable [IsAutoAssociatedRing R]

namespace IsAutoAssociatedRing

/-- Lemma 15.15.2: in an auto-associated ring, every proper finitely generated ideal has nonzero
annihilator ideal. This is the property `(P)` of an auto-associated ring. -/
theorem annihilator_ne_bot_of_fg_of_ne_top {I : Ideal R} (hI : I.FG) (hproper : I ≠ ⊤) :
    I.annihilator ≠ ⊥ := by
  obtain ⟨x, hxdef⟩ :
      ∃ x : R, (torsionOf R R x).IsIdealOfDefinition :=
    exists_torsionOf_isIdealOfDefinition
  exact
    Ideal.annihilator_ne_bot_of_fg_of_ne_top_of_torsionOf_isIdealOfDefinition x hxdef hI hproper

end IsAutoAssociatedRing

end

end
