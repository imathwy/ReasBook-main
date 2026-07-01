import Mathlib
import stacks_project.Chap10.Lemma_10_24_1

-- Declarations for this item will be appended below by the statement pipeline.

open LinearMap

universe u v w

noncomputable section

section

variable {R : Type u} [CommRing R]
variable {ι : Type w}
variable (M : Type v) [AddCommGroup M] [Module R M] [Finite ι] (f : ι → R)

-- Proof sketch: if the canonical map to the family of away localizations is injective and every
-- component of the product linear map `pi fun i ↦ DistribSMul.toLinearMap R M (f i)` vanishes on
-- `m`, then the image of `m` in each `M_{f_i}` is zero, so `m = 0`. Conversely, if this product
-- linear map is injective and the image of `m` in each `M_{f_i}` vanishes, then some power of
-- each `f i` kills `m`; use induction on the finite sum of these exponents to reduce to the case
-- where every exponent is `1`.
/-- Bridge the injectivity of the canonical map to the family of away localizations with the
vanishing of the torsion submodule cut out by the generating set `Set.range f`. -/
theorem away_localization_family_map_injective_iff_torsionBySet_eq_bot :
    Function.Injective (awayLocalizationFamilyMap M f) ↔
      Submodule.torsionBySet R M (Set.range f) = ⊥ := sorry

/-- Lemma 10.24.4: for a finite family `f : ι → R`, the canonical map from `M` to the family of
away localizations `M_{f_i}` is injective if and only if the product linear map with components
`m ↦ f_i • m` is injective. The Stacks Project writes the targets as finite direct sums; in Lean
we use the canonically equivalent finite products `∀ i, LocalizedModule.Away (f i) M` and
`∀ i, M`. -/
theorem away_localization_family_map_injective_iff_smul_family_map_injective :
    Function.Injective (awayLocalizationFamilyMap M f) ↔
      Function.Injective (LinearMap.pi fun i ↦ DistribSMul.toLinearMap R M (f i)) := by
  have hker :
      LinearMap.ker (LinearMap.pi fun i ↦ DistribSMul.toLinearMap R M (f i)) =
        Submodule.torsionBySet R M (Set.range f) := by
    ext m
    rw [LinearMap.ker_pi, Submodule.mem_iInf, Submodule.mem_torsionBySet_iff]
    constructor
    · intro hm ⟨a, ha⟩
      rcases ha with ⟨i, rfl⟩
      simpa [LinearMap.mem_ker] using hm i
    · intro hm i
      simpa [LinearMap.mem_ker] using hm ⟨f i, Set.mem_range_self i⟩
  have hsmul :
      Function.Injective (LinearMap.pi fun i ↦ DistribSMul.toLinearMap R M (f i)) ↔
        Submodule.torsionBySet R M (Set.range f) = ⊥ := by
    rw [← LinearMap.ker_eq_bot, hker]
  exact (away_localization_family_map_injective_iff_torsionBySet_eq_bot M f).trans hsmul.symm

end
