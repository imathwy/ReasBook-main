import Mathlib
import Serre.Chap10.Definition_10_10_1_3
import Serre.Chap12.Theorem_12_12_4_1.GammaSubgroupAction

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

universe u

section Group

open Representation

variable {G : Type u} [Group G]

namespace Subgroup

-- Source/core/bridge triage:
-- * source-facing: `IsGammaPElementaryDecomposition ΓK p C P`, `IsGammaPElementary ΓK p H`, and
--   `IsGammaElementary ΓK H`.
-- * core/canonical: `IsPGroup`, `Subgroup.IsComplement'`, and the Chapter 10 owner
--   `IsPElementaryDecomposition` used for the trivial-`Γ_K` comparison.
-- * bridge/view: the `Γ_K = ⊥` comparison with ordinary `p`-elementary subgroups.
--
-- Relative to Chapter 10, the genuinely new primitive datum is the `Γ_K`-power-conjugation
-- condition. The subgroup-theoretic decomposition data stay in the same canonical owner layer as
-- before: prime `p`, finite `p`-group factor, cyclic prime-to-`p` factor, and complementarity.

/-- Helper for Definition 12-12.6-1: the natural-number representative of a `Γ_K` exponent unit.
-/
private abbrev gamma_power_exponent_unit
    {ΓK : Subgroup (ZMod (Monoid.exponent G))ˣ} (t : ΓK) : ℕ :=
  ((t : (ZMod (Monoid.exponent G))ˣ) : ZMod (Monoid.exponent G)).val

/-- Helper for Definition 12-12.6-1: elements of `Γ_K` act on `G` by exponentiation using their
chosen representatives modulo `Monoid.exponent G`. -/
private instance gammaSubgroupPow
    {ΓK : Subgroup (ZMod (Monoid.exponent G))ˣ} : Pow G ΓK where
  pow x t := x ^ gamma_power_exponent_unit (G := G) t

/-- Helper for Definition 12-12.6-1: the `Γ_K` power action unfolds to ordinary natural-number
exponentiation. -/
private theorem pow_subgroup_eq_pow_nat
    {ΓK : Subgroup (ZMod (Monoid.exponent G))ˣ} (x : G) (t : ΓK) :
    (x ^ t : G) = x ^ gamma_power_exponent_unit (G := G) t := rfl

/-- A pair of subgroups `C` and `P` inside `H` gives a `Γ_K`-`p`-elementary decomposition if `p`
is prime, `C` is cyclic of order prime to `p`, `P` is a finite `p`-group, `C` and `P` are
complementary in `H`, and conjugation by every element of `P` acts on `C` through a power map
coming from `Γ_K`. -/
def IsGammaPElementaryDecomposition (ΓK : Subgroup (ZMod (Monoid.exponent G))ˣ) (p : ℕ)
    {H : Subgroup G} (C P : Subgroup H) : Prop :=
  Nat.Prime p ∧
    Finite P ∧
      IsCyclic C ∧
        Nat.Coprime p (Nat.card C) ∧
          IsPGroup p P ∧
            C.IsComplement' P ∧
              ∀ y : P, ∃ t : ΓK, ∀ x : C,
                (((y : H) : G) * ((x : H) : G) * ((y : H) : G)⁻¹ =
                  ((x : H) : G) ^ t)

namespace IsGammaPElementaryDecomposition

variable {ΓK : Subgroup (ZMod (Monoid.exponent G))ˣ} {p : ℕ} {H : Subgroup G} {C P : Subgroup H}

/-- The prime attached to a `Γ_K`-`p`-elementary decomposition. -/
theorem prime (h : IsGammaPElementaryDecomposition ΓK p C P) : Nat.Prime p := by
  rcases h with ⟨hp, -, -, -, -, -, -⟩
  exact hp

/-- Helper for Definition 12-12.6-1: the cyclic factor in a `Γ_K`-`p`-elementary decomposition
is finite. -/
theorem finite_cyclic_factor (h : IsGammaPElementaryDecomposition ΓK p C P) : Finite C := by
  rcases h with ⟨hp, -, -, hcoprime, -, -, -⟩
  by_contra hC
  -- An infinite cyclic factor has `Nat.card C = 0`, contradicting coprimality with a prime.
  have hInf : Infinite C := not_finite_iff_infinite.mp hC
  letI : Infinite C := hInf
  have hc : Nat.Coprime p 0 := by
    simpa [Nat.card_eq_zero_of_infinite] using hcoprime
  rw [Nat.coprime_zero_right] at hc
  exact hp.ne_one hc

/-- The `p`-group factor in a `Γ_K`-`p`-elementary decomposition is finite. -/
theorem finite_pGroup_factor (h : IsGammaPElementaryDecomposition ΓK p C P) : Finite P := by
  rcases h with ⟨-, hP, -, -, -, -, -⟩
  exact hP

/-- The cyclic factor in a `Γ_K`-`p`-elementary decomposition is cyclic. -/
theorem cyclic (h : IsGammaPElementaryDecomposition ΓK p C P) : IsCyclic C := by
  rcases h with ⟨-, -, hC, -, -, -, -⟩
  exact hC

/-- The cyclic factor has order prime to `p`. -/
theorem coprime_card (h : IsGammaPElementaryDecomposition ΓK p C P) :
    Nat.Coprime p (Nat.card C) := by
  rcases h with ⟨-, -, -, hcoprime, -, -, -⟩
  exact hcoprime

/-- The second factor is a `p`-group. -/
theorem isPGroup (h : IsGammaPElementaryDecomposition ΓK p C P) : IsPGroup p P := by
  rcases h with ⟨-, -, -, -, hP, -, -⟩
  exact hP

/-- Conjugation by elements of the `p`-group factor acts on the cyclic factor by `Γ_K`-power
maps. -/
theorem conjugation_eq_pow (h : IsGammaPElementaryDecomposition ΓK p C P) :
    ∀ y : P, ∃ t : ΓK, ∀ x : C,
      (((y : H) : G) * ((x : H) : G) * ((y : H) : G)⁻¹ =
        ((x : H) : G) ^ t) :=
  by
    rcases h with ⟨-, -, -, -, -, -, hgamma⟩
    exact hgamma

/-- The two factors are complementary subgroups of `H`. -/
theorem isComplement (h : IsGammaPElementaryDecomposition ΓK p C P) : C.IsComplement' P := by
  rcases h with ⟨-, -, -, -, -, hcomp, -⟩
  exact hcomp

@[simp] theorem pow_bot_eq_self
    (x : G) (t : (⊥ : Subgroup (ZMod (Monoid.exponent G))ˣ)) :
    x ^ t = x := by
  have ht : t = 1 := Subsingleton.elim _ _
  subst ht
  rw [pow_subgroup_eq_pow_nat]
  change x ^ (((1 : (ZMod (Monoid.exponent G))ˣ) : ZMod (Monoid.exponent G)).val) = x
  have hpow : x ^ (1 % Monoid.exponent G) = x ^ 1 := by
    simpa using (Eq.symm (@Monoid.pow_eq_mod_exponent G _ 1 x))
  simpa [ZMod.val_one_eq_one_mod] using hpow

/-- For `Γ_K = {1}`, a `Γ_K`-`p`-elementary decomposition is exactly an ordinary
`p`-elementary decomposition. -/
theorem bot_iff_isPElementaryDecomposition :
    IsGammaPElementaryDecomposition (⊥ : Subgroup (ZMod (Monoid.exponent G))ˣ) p C P ↔
      IsPElementaryDecomposition p C P := by
  constructor
  · intro h
    refine ⟨h.prime, h.finite_pGroup_factor, h.cyclic, h.coprime_card, h.isPGroup, ?_,
      h.isComplement⟩
    rw [Subgroup.le_centralizer_iff]
    intro y hy
    rw [Subgroup.mem_centralizer_iff]
    intro x hx
    rcases h.conjugation_eq_pow ⟨y, hy⟩ with ⟨t, ht⟩
    have hxpow : ((x : H) : G) ^ t = ((x : H) : G) := pow_bot_eq_self _ _
    have hconj : ((y : H) : G) * ((x : H) : G) * ((y : H) : G)⁻¹ = ((x : H) : G) := by
      simpa [hxpow] using ht ⟨x, hx⟩
    have hcomm : ((y : H) : G) * ((x : H) : G) = ((x : H) : G) * ((y : H) : G) :=
      (mul_inv_eq_iff_eq_mul).mp (by simpa [mul_assoc] using hconj)
    apply Subtype.ext
    exact hcomm.symm
  · intro h
    refine ⟨h.prime, h.finite_pGroup_factor, h.cyclic, h.coprime_card, h.isPGroup,
      h.isComplement, ?_⟩
    intro y
    let tOne : (⊥ : Subgroup (ZMod (Monoid.exponent G))ˣ) := ⟨1, by simp⟩
    refine ⟨tOne, ?_⟩
    intro x
    have hyx : ((y : H) : G) * ((x : H) : G) = ((x : H) : G) * ((y : H) : G) := by
      simpa using congrArg (fun z : H ↦ ((z : H) : G))
        (h.commute x y).eq.symm
    have hxpow : ((x : H) : G) ^ tOne = ((x : H) : G) := pow_bot_eq_self _ _
    calc
      ((y : H) : G) * ((x : H) : G) * ((y : H) : G)⁻¹
          = ((x : H) : G) * ((y : H) : G) * ((y : H) : G)⁻¹ := by rw [hyx]
      _ = ((x : H) : G) := by simp [mul_assoc]
      _ = ((x : H) : G) ^ tOne := by
        symm
        exact hxpow

end IsGammaPElementaryDecomposition

/-- A subgroup `H` of `G` is `Γ_K`-`p`-elementary if it admits a `Γ_K`-`p`-elementary
decomposition by a cyclic prime-to-`p` factor and a finite `p`-group factor whose conjugation
action is given by `Γ_K`-power maps. -/
def IsGammaPElementary (ΓK : Subgroup (ZMod (Monoid.exponent G))ˣ) (p : ℕ)
    (H : Subgroup G) : Prop :=
  ∃ C P : Subgroup H, IsGammaPElementaryDecomposition ΓK p C P

/-- Definition 12-12.6-1: a subgroup `H` of `G` is `Γ_K`-elementary if it is `Γ_K`-`p`-elementary
for some prime number `p`. -/
def IsGammaElementary (ΓK : Subgroup (ZMod (Monoid.exponent G))ˣ) (H : Subgroup G) : Prop :=
  ∃ p : ℕ, IsGammaPElementary ΓK p H

-- Proof sketch: unfold `IsGammaPElementary` and read off the cyclic factor `C`, the `p`-group
-- factor `P`, and the accompanying `Γ_K`-power-conjugation condition from the existential data.
theorem IsGammaPElementary.prime
    {ΓK : Subgroup (ZMod (Monoid.exponent G))ˣ} {p : ℕ} {H : Subgroup G}
    (hH : IsGammaPElementary ΓK p H) : Nat.Prime p := by
  rcases hH with ⟨_, _, h⟩
  exact h.prime

/-- A `Γ_K`-`p`-elementary subgroup is, in particular, `Γ_K`-elementary. -/
theorem IsGammaPElementary.isGammaElementary
    {ΓK : Subgroup (ZMod (Monoid.exponent G))ˣ} {p : ℕ} {H : Subgroup G}
    (hH : IsGammaPElementary ΓK p H) :
    IsGammaElementary ΓK H :=
  ⟨p, hH⟩

-- Proof sketch: unfold `IsGammaElementary` and keep the prime `p` together with the witness that
-- `H` is `Γ_K`-`p`-elementary.
/-- A `Γ_K`-elementary subgroup is `Γ_K`-`p`-elementary for some prime `p`. -/
theorem IsGammaElementary.exists_prime_and_pElementary
    {ΓK : Subgroup (ZMod (Monoid.exponent G))ˣ} {H : Subgroup G} (hH : IsGammaElementary ΓK H) :
    ∃ p : ℕ, Nat.Prime p ∧ IsGammaPElementary ΓK p H := by
  rcases hH with ⟨p, hp⟩
  exact ⟨p, hp.prime, hp⟩

-- Proof sketch: if `Γ_K = {1}`, then the only allowed power map is the identity modulo
-- `Monoid.exponent G`, so the conjugation condition says that the cyclic factor commutes with the
-- `p`-group factor; this is exactly Serre's earlier definition of an ordinary `p`-elementary
-- subgroup, and conversely.
/-- For the trivial subgroup `Γ_K = {1}`, `Γ_K`-`p`-elementary subgroups are exactly the ordinary
`p`-elementary subgroups from Chapter 10. -/
theorem IsGammaPElementary.bot_iff_isPElementary
    (p : ℕ) (H : Subgroup G) :
    IsGammaPElementary (⊥ : Subgroup (ZMod (Monoid.exponent G))ˣ) p H ↔ IsPElementary p H := by
  constructor
  · rintro ⟨C, P, h⟩
    exact ⟨C, P, IsGammaPElementaryDecomposition.bot_iff_isPElementaryDecomposition.mp h⟩
  · rintro ⟨C, P, h⟩
    exact ⟨C, P, IsGammaPElementaryDecomposition.bot_iff_isPElementaryDecomposition.mpr h⟩

end Subgroup

end Group
