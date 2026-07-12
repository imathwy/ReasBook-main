import Mathlib.RingTheory.GradedAlgebra.Radical
import Mathlib.RingTheory.Ideal.MinimalPrime.Basic
import Mathlib.Tactic.StacksAttribute

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

section

open Ideal

variable {S : Type u} {σ : Type v}
variable [CommRing S] [SetLike σ S] [AddSubmonoidClass σ S]
variable (𝒜 : ℕ → σ) [GradedRing 𝒜]

/-- Lemma 10.57.8 (2) (Stacks, Tag `00JU`): if `I` is a homogeneous ideal of an `ℕ`-graded
commutative ring `S`, then every minimal prime ideal over `I` is homogeneous. -/
-- Proof sketch: for a minimal prime `𝔭` over `I`, the canonical theorem
-- `Ideal.IsPrime.homogeneousCore` shows that `(𝔭.homogeneousCore 𝒜).toIdeal` is again prime.
-- Since `I` is homogeneous and `I ≤ 𝔭`, we have
-- `I ≤ (𝔭.homogeneousCore 𝒜).toIdeal ≤ 𝔭`. Minimality of `𝔭` among primes over `I` forces equality,
-- so `𝔭` equals its homogeneous core and is therefore homogeneous.
@[stacks 00JU]
theorem isHomogeneous_of_mem_minimalPrimes_of_isHomogeneous
    {I 𝔭 : Ideal S} (hI : I.IsHomogeneous 𝒜) (h𝔭 : 𝔭 ∈ I.minimalPrimes) :
    𝔭.IsHomogeneous 𝒜 := by
  have hIcore : I ≤ (𝔭.homogeneousCore 𝒜).toIdeal := by
    rw [← hI.toIdeal_homogeneousCore_eq_self]
    exact homogeneousCore_mono 𝒜 h𝔭.1.2
  have h𝔭core : 𝔭 ≤ (𝔭.homogeneousCore 𝒜).toIdeal :=
    h𝔭.2 ⟨h𝔭.1.1.homogeneousCore, hIcore⟩ (toIdeal_homogeneousCore_le 𝒜 𝔭)
  exact (IsHomogeneous.iff_eq 𝒜 𝔭).2 <| le_antisymm (toIdeal_homogeneousCore_le 𝒜 𝔭) h𝔭core

/-- Lemma 10.57.8 (1) (Stacks, Tag `00JU`): every minimal prime of an `ℕ`-graded commutative ring
is homogeneous. -/
@[stacks 00JU]
theorem isHomogeneous_of_mem_minimalPrimes {𝔭 : Ideal S} (h𝔭 : 𝔭 ∈ minimalPrimes S) :
    𝔭.IsHomogeneous 𝒜 := by
  simpa [minimalPrimes] using
    isHomogeneous_of_mem_minimalPrimes_of_isHomogeneous 𝒜 (IsHomogeneous.bot 𝒜) h𝔭

end
