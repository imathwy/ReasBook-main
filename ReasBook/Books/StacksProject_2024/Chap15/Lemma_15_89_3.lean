import Mathlib.Data.List.TFAE
import StacksProject_2024.Chap10.Lemma_10_24_4
import StacksProject_2024.Chap15.Definition_15_89_1

-- Declarations for this item will be appended below by the statement pipeline.

universe u v w

section

open scoped IdealPowerTorsion

variable {R : Type u} [CommRing R]
variable {M : Type v} [AddCommGroup M] [Module R M]
variable {I : Ideal R}
variable {ι : Type w} [Finite ι]

/- Domain-style sampling:
- primary domain: commutative algebra of ideal-power torsion and away localizations;
- sampled owner declarations:
  `Ideal.powerTorsion`,
  `Module.IsIdealPowerTorsion`,
  `Submodule.torsionBySet`,
  `awayLocalizationFamilyMap`,
  `Submodule.torsionBySet_eq_torsionBySet_span`,
  `away_localization_family_map_injective_iff_torsionBySet_eq_bot`;
- best owner abstraction: the source-facing Chapter `15` finite-stage owner is
  `Ideal.powerTorsion`, whose core owner is `Submodule.torsionBySet`; the Chapter `10` owner
  `awayLocalizationFamilyMap` and the bridge
  `away_localization_family_map_injective_iff_torsionBySet_eq_bot`;
- primitive data: the ideal `I` together with a finite generating family `f` satisfying
  `Ideal.span (Set.range f) = I`;
- derived API: the vanishing conditions `M[I^1] = ⊥` and
  `∀ n : ℕ+, M[I^(n : ℕ)] = ⊥`, together with injectivity of
  `awayLocalizationFamilyMap M f`, packaged as a local `List.TFAE`.

Layer triage:
- `source-facing`: the three equivalent conditions in Stacks Lemma `15.89.3`;
- `core/canonical`: `Submodule.torsionBySet`;
- `bridge/view`: the Chapter `10` away-localization injectivity criteria.
-/

-- Proof sketch: when `I = Ideal.span (Set.range f)`, the chapter bridge
-- `away_localization_family_map_injective_iff_torsionBySet_eq_bot` together with
-- `Submodule.torsionBySet_eq_torsionBySet_span` identifies the base case
-- `I.powerTorsion M 1 = ⊥` with injectivity of the canonical map
-- `awayLocalizationFamilyMap M f`. For higher powers, if
-- `I^(n + 2)` kills `x`, then `I^(n + 1)` kills each `f i • x`; induction on `n` and injectivity
-- of the smul family map show `x = 0`.

/-- Bridge lemma: if `f` spans `I` and the canonical map to the away localizations `M_{f_i}` is
injective, then every positive-power torsion submodule `M[I^n]` vanishes. -/
theorem powerTorsionSubmodule_eq_bot_of_injective_awayLocalizationFamilyMap (f : ι → R)
    (hI : Ideal.span (Set.range f) = I)
    (hloc : Function.Injective (awayLocalizationFamilyMap M f)) (n : ℕ+) :
    M[I^(n : ℕ)] = ⊥ := by
  have hf_mem : ∀ i, f i ∈ I := fun i ↦ by
    simpa [hI] using (Ideal.subset_span (Set.mem_range_self i) : f i ∈ Ideal.span (Set.range f))
  let smulFamilyMap : M →ₗ[R] ∀ i, M := LinearMap.pi fun i ↦
    DistribSMul.toLinearMap R M (f i)
  have hsmul : Function.Injective smulFamilyMap := by
    simpa [smulFamilyMap] using
      (away_localization_family_map_injective_iff_smul_family_map_injective M f).mp hloc
  have hpow : ∀ m : ℕ, Submodule.torsionBySet R M ↑(I ^ (m + 1)) = ⊥ := by
    intro m
    induction m with
    | zero =>
        change Submodule.torsionBySet R M ↑(I ^ 1) = ⊥
        simpa [Submodule.torsionBySet_eq_torsionBySet_span, hI] using
          (away_localization_family_map_injective_iff_torsionBySet_eq_bot M f).mp hloc
    | succ m hm =>
        exact (Submodule.eq_bot_iff _).2 fun x hx ↦ by
          apply hsmul
          ext i
          have hfx : f i • x ∈ Submodule.torsionBySet R M ↑(I ^ (m + 1)) := by
            change x ∈ Submodule.torsionBySet R M ↑(I ^ (m + 2)) at hx
            change f i • x ∈ Submodule.torsionBySet R M ↑(I ^ (m + 1))
            rw [Submodule.mem_torsionBySet_iff] at hx ⊢
            intro a
            have hmul : f i * (a : R) ∈ I ^ (m + 2) := by
              simpa [pow_succ, mul_assoc, mul_comm, mul_left_comm] using
                (Ideal.mul_mem_mul a.2 (hf_mem i) : (a : R) * f i ∈ I ^ (m + 1) * I)
            simpa [smul_smul, mul_comm] using hx ⟨f i * a, hmul⟩
          simpa [hm] using hfx
  have hn : ((n : ℕ) - 1) + 1 = (n : ℕ) := Nat.sub_add_cancel (Nat.succ_le_of_lt n.2)
  simpa [hn] using hpow ((n : ℕ) - 1)

/-- Lemma 15.89.3: for a finitely generated ideal written as `I = Ideal.span (Set.range f)`, the
vanishing of `M[I^1]`, the vanishing of all higher power-torsion submodules `M[I^n]` for
`n ≥ 1`, and injectivity of the canonical localization-family map `awayLocalizationFamilyMap M f`
from `M` to the family of away localizations `M_{f_i}` are equivalent. -/
theorem ideal_power_torsion_bot_tfae_of_span_eq (f : ι → R)
    (hI : Ideal.span (Set.range f) = I) :
    List.TFAE [
      M[I^1] = ⊥,
      ∀ n : ℕ+, M[I^(n : ℕ)] = ⊥,
      Function.Injective (awayLocalizationFamilyMap M f)
    ] := by
  tfae_have 1 ↔ 3 := by
    simpa [Submodule.torsionBySet_eq_torsionBySet_span, hI] using
      (away_localization_family_map_injective_iff_torsionBySet_eq_bot M f).symm
  tfae_have 3 → 2 := by
    intro hloc n
    exact powerTorsionSubmodule_eq_bot_of_injective_awayLocalizationFamilyMap f hI hloc n
  tfae_have 2 → 1 := by
    intro h
    simpa using h 1
  tfae_finish

end
