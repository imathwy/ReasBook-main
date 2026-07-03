import Mathlib
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

/-
Domain-style sampling:
- primary domain: torsion theory for modules over commutative semirings, with the source-facing
  nonzero-scalar reformulation specialized to domains;
- sampled owner API:
  `Submodule.torsion`,
  `Submodule.mem_torsion_iff`,
  `Submodule.isTorsionFree_iff_torsion_eq_bot`,
  `Submodule.isTorsion'_iff_torsion'_eq_top`;
- best owner abstraction: `Submodule.torsion`, with proposition-level owners
  `Module.IsTorsionFree` and `Module.IsTorsion`;
- source-facing layer: textbook restatements describing torsion elements, torsion-free modules, and
  torsion modules in terms of membership in `Submodule.torsion`;
- core/canonical layer: the upstream mathlib owners listed above;
- bridge/view layer: the local textbook reformulations below.

Primitive data are only the ambient ring and module. The torsion submodule itself and the
proposition-level torsion / torsion-free owners are already canonical upstream, so this file should
recall `Submodule.torsion` directly and keep only the source-facing bridge statements that change
the surface wording from `R⁰`-annihilators to nonzero scalars or to membership in the torsion
submodule. In particular, `Submodule.torsion`, `Submodule.mem_torsion_iff`, and the torsion-owner
bridge live at the `CommSemiring` / `AddCommMonoid` level; only the domain-specific restatement in
terms of nonzero scalars needs `IsDomain`, while the torsion-free bridge through
`Submodule.isTorsionFree_iff_torsion_eq_bot` still lives at the `CommRing` / `AddCommGroup` level.
-/

section

open Module

section Domain

variable {R : Type u} [CommSemiring R] [IsDomain R]
variable {M : Type v} [AddCommMonoid M] [Module R M]

/- Definition 15.22.1: over a domain, the canonical torsion submodule `Submodule.torsion R M`
collects exactly the torsion elements of `M`, i.e. those annihilated by some nonzero scalar. -/
recall Submodule.torsion

-- Proof sketch: unfold `Submodule.torsion`; in a domain, non-zero-divisors are exactly the
-- nonzero scalars, so membership is equivalent to the existence of a nonzero annihilator.
/-- An element of a module over a domain is torsion exactly when it lies in the canonical torsion
submodule. -/
theorem mem_torsion_iff_exists_ne_zero_smul_eq_zero (x : M) :
    x ∈ Submodule.torsion R M ↔ ∃ f : R, f ≠ 0 ∧ f • x = 0 := by
  constructor
  · rintro ⟨f, hf⟩
    exact ⟨f, mem_nonZeroDivisors_iff_ne_zero.mp f.2, hf⟩
  · rintro ⟨f, hf0, hf⟩
    exact ⟨⟨f, mem_nonZeroDivisors_iff_ne_zero.mpr hf0⟩, hf⟩

end Domain

section DomainRing

variable {R : Type u} [CommRing R] [IsDomain R]
variable {M : Type v} [AddCommGroup M] [Module R M]

-- Proof sketch: use the canonical owner theorem
-- `Submodule.isTorsionFree_iff_torsion_eq_bot` and rewrite `Submodule.torsion R M = ⊥` as the
-- statement that every torsion element is zero.
/-- A module over a domain is torsion-free exactly when its only torsion element is `0`. -/
theorem isTorsionFree_iff_forall_mem_torsion_eq_zero :
    IsTorsionFree R M ↔ ∀ x : M, x ∈ Submodule.torsion R M → x = 0 := by
  rw [Submodule.isTorsionFree_iff_torsion_eq_bot, Submodule.eq_bot_iff]

/-- Over a Noetherian domain, a torsion-free module has no nonzero associated primes. -/
theorem Module.not_mem_associatedPrimes_of_ne_bot [IsNoetherianRing R] [IsTorsionFree R M]
    {p : Ideal R} (hp : p ≠ ⊥) : p ∉ associatedPrimes R M := by
  intro hp_assoc
  have hp_not_le : ¬ p ≤ (⊥ : Ideal R) := by
    intro h
    exact hp (le_antisymm h bot_le)
  rw [SetLike.not_le_iff_exists] at hp_not_le
  obtain ⟨r, hrp, hr0⟩ := hp_not_le
  have hr_zeroDiv : r ∈ { a : R | ∃ x : M, x ≠ 0 ∧ a • x = 0 } := by
    rw [← biUnion_associatedPrimes_eq_zero_divisors R M]
    exact Set.mem_iUnion_of_mem p <| Set.mem_iUnion_of_mem hp_assoc hrp
  rcases hr_zeroDiv with ⟨x, hx0, hrx⟩
  exact hr0 ((smul_eq_zero.mp hrx).resolve_right hx0)

end DomainRing

section Semiring

variable {R : Type u} [CommSemiring R]
variable {M : Type v} [AddCommMonoid M] [Module R M]

-- Proof sketch: `Module.IsTorsion` and membership in `Submodule.torsion` are already equivalent
-- via the canonical owner lemma `Submodule.mem_torsion_iff`, so no domain hypothesis is needed.
/-- An `R`-module is torsion exactly when every element is torsion. -/
theorem isTorsion_iff_forall_mem_torsion :
    IsTorsion R M ↔ ∀ x : M, x ∈ Submodule.torsion R M := by
  simp [Module.IsTorsion]

end Semiring

end
