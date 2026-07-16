import Mathlib
import StacksProject_2024.stacks_project.Chap10.Lemma_10_62_4
import StacksProject_2024.stacks_project.Chap15.Definition_15_89_1

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

namespace Module

section

open PrimeSpectrum

variable {R : Type u} [CommRing R]
variable {M : Type v} [AddCommGroup M] [Module R M]

/-
Domain-style sampling pass for Lemma 15.89.6.

Primary domain: commutative algebra of ideal-power torsion modules and support in `Spec R`.

Sampled owner declarations:
* `Module.IsIdealPowerTorsion` and `Module.isIdealPowerTorsion_iff` from
  `Definition_15_89_1.lean`;
* `Module.support` and `Module.support_subset_of_injective`;
* `Module.exists_pow_le_annihilator_iff_support_subset_zeroLocus` from
  `Lemma_10_62_4.lean`.

Best owner abstraction: the source-facing predicate `Module.IsIdealPowerTorsion I M` together with
the canonical support owner `Module.support R M`. The cyclic-submodule annihilator criterion is
derived API used only as the bridge from support containment to elementwise torsion.

Source/core/bridge triage:
* `source-facing`: the Stacks equivalence between `I`-power torsion and support contained in
  `V(I)`;
* `core/canonical`: `Module.IsIdealPowerTorsion` and `Module.support`;
* `bridge/view`: the finite cyclic-module support criterion
  `exists_pow_le_annihilator_iff_support_subset_zeroLocus`.
-/

-- Proof sketch: use `Module.isIdealPowerTorsion_iff` to unpack `I`-power torsion elementwise.
-- If `p ∈ support R M`, the owner theorem `Module.mem_support_iff_exists_annihilator` produces an
-- element whose cyclic submodule has annihilator contained in `p`; any `f ∈ I \ p` would then
-- give a contradiction, because some power of `f` kills that element. Conversely, if the support
-- is contained in `V(I)`, then each cyclic submodule `R ∙ x` has support in `V(I)`; applying the
-- finite-module support criterion from Lemma `10.62.4` to `R ∙ x` produces a power of `I`
-- contained in the annihilator of `R ∙ x`, hence killing `x`.
/-- Lemma 15.89.6: for a finitely generated ideal `I`, an `R`-module `M` is `I`-power torsion,
equivalently `M[I^∞] = ⊤`, if and only if its support is contained in `V(I)`. -/
theorem isIdealPowerTorsion_iff_support_subset_zeroLocus
    (I : Ideal R) (hI : I.FG) :
    IsIdealPowerTorsion I M ↔ support R M ⊆ zeroLocus I := by
  rw [isIdealPowerTorsion_iff]
  constructor
  · intro hM p hp
    rw [mem_zeroLocus]
    by_contra hpI
    obtain ⟨f, hfI, hfp⟩ := Set.not_subset.mp hpI
    obtain ⟨m, hm⟩ := mem_support_iff_exists_annihilator.mp hp
    obtain ⟨n, hn⟩ := hM m
    have hpow : (f ^ (n : ℕ)) • m = 0 :=
      hn ⟨f ^ (n : ℕ), Ideal.pow_mem_pow hfI _⟩
    have hfpow : f ^ (n : ℕ) ∈ p.asIdeal := hm <|
      (Submodule.mem_annihilator_span_singleton _ _).mpr hpow
    exact hfp (p.isPrime.mem_of_pow_mem _ hfpow)
  · intro hM x
    set N : Submodule R M := R ∙ x
    haveI : Module.Finite R N := by
      simpa [N] using
        (Module.Finite.of_fg (Submodule.fg_span_singleton x) : Module.Finite R (R ∙ x : Submodule R M))
    have hNSupport : support R N ⊆ zeroLocus I :=
      (support_subset_of_injective N.subtype N.subtype_injective).trans hM
    obtain ⟨n, hn⟩ :=
      (exists_pow_le_annihilator_iff_support_subset_zeroLocus I hI).mpr hNSupport
    refine ⟨⟨n + 1, Nat.succ_pos n⟩, fun a ↦ ?_⟩
    have ha : (a : R) ∈ annihilator R N :=
      hn <| Ideal.pow_le_pow_right (Nat.le_succ n) a.2
    simpa [N] using (Submodule.mem_annihilator_span_singleton x (a : R)).mp ha

end

end Module
