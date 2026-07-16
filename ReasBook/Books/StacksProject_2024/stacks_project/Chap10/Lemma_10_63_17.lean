import StacksProject_2024.stacks_project.Chap10.Lemma_10_63_16

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

section

open Module.associatedPrimes IsLocalizedModule

variable {R : Type u} [CommRing R]
variable {M : Type v} [AddCommGroup M] [Module R M]
variable (S : Submonoid R)

local notation "Mₛ" => LocalizedModule S M

/- Domain triage:
- primary domain: commutative algebra of associated primes under localization;
- `source-facing`: the textbook exact-annihilator set `associatedPrimesOfModule R M`;
- `core/canonical`: mathlib's radical-based owner set `associatedPrimes R M` in the Noetherian
  case;
- primitive data: the canonical localization map `LocalizedModule.mkLinearMap S M` together with
  regularity of the `S`-action on `M`;
- derived API: equalities of the associated-prime sets. This file should stay a thin source-facing
  theorem plus its Noetherian owner companion, with no extra wrapper layer.
-/

/-- Lemma 10.63.17: if every element of the multiplicative set `S` is a nonzerodivisor on the
`R`-module `M`, then the associated primes of `M` agree with those of the localized module
`S⁻¹M` viewed as an `R`-module. -/
-- Proof sketch: the hypothesis is exactly the injectivity criterion for the canonical localization
-- map `M → S⁻¹M`, so the annihilator of `m` agrees with the annihilator of its image. For the
-- reverse inclusion, write a localized witness as `m / s`; if `r (m / s) = 0`, then after
-- clearing denominators some `s' ∈ S` kills `r m`, and regularity of `s'` forces `r m = 0`.
@[stacks 05C0]
theorem associatedPrimesOfModule_eq_associatedPrimesOfModule_localizedModule
    (hS : ∀ s : S, IsSMulRegular M s) :
    associatedPrimesOfModule R M = associatedPrimesOfModule R Mₛ := by
  let f : M →ₗ[R] Mₛ := LocalizedModule.mkLinearMap S M
  refine Set.Subset.antisymm ?_ ?_
  · intro p hp
    have hf : Function.Injective f := (injective_iff_isRegular S f).2 hS
    simpa [associatedPrimesOfModule] using Ideal.isAssociatedToModule_map_of_injective R M hp f hf
  · intro p hp
    rcases hp with ⟨hp, x, hx⟩
    obtain ⟨⟨m, s⟩, rfl⟩ := mk'_surjective S f x
    simp only [Function.uncurry_apply_pair] at hx
    refine ⟨hp, m, ?_⟩
    ext r
    rw [hx, Ideal.mem_torsionOf_iff, Ideal.mem_torsionOf_iff]
    constructor
    · intro hr
      have hs : mk' f (r • m) s = 0 := by
        simpa [mk'_smul] using hr
      rcases (mk'_eq_zero' f s).mp hs with ⟨s', hs'⟩
      exact (hS s').right_eq_zero_of_smul hs'
    · intro hr
      rw [← mk'_smul, hr, mk'_zero]

/-- In the Noetherian case, Lemma 10.63.17 specializes to the canonical mathlib set
`associatedPrimes`. -/
theorem associatedPrimes_eq_associatedPrimes_localizedModule [IsNoetherianRing R]
    (hS : ∀ s : S, IsSMulRegular M s) :
    associatedPrimes R M = associatedPrimes R Mₛ := by
  rw [← associatedPrimesOfModule_eq_associatedPrimes R M,
    ← associatedPrimesOfModule_eq_associatedPrimes R Mₛ]
  exact associatedPrimesOfModule_eq_associatedPrimesOfModule_localizedModule S hS

end
