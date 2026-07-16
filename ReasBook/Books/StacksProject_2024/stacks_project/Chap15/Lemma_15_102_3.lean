import Mathlib
import StacksProject_2024.stacks_project.Chap15.Lemma_15_102_2

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory.Abelian
open CategoryTheory.Abelian.Ext
open scoped IdealPowerSubmodule

universe u

noncomputable section

attribute [local instance] CategoryTheory.HasExt.standard

section

variable {A : Type u} [CommRing A] [IsNoetherianRing A]

/- Domain-style sampling:
- primary domain: Ext-groups of finite modules over a Noetherian ring, with the restriction map
  induced by the inclusion `I^n M ↪ M`;
- sampled owner declarations:
  `idealPowerSubtype`,
  `idealPowerSubtypeExtPrecomp`,
  `idealPowerSubtypeExtPostcomp`,
  `exists_ext_factorization_through_ideal_power_target`;
- best owner abstraction: the chapter owner `idealPowerSubtypeExtPrecomp` is the canonical
  restriction map on Ext for the ideal-power inclusion, and Lemma `15.102.2` already supplies the
  needed factorization through `Ext^p_A(I^n M, I^(n - c) N)`;
- primitive data: the ideal `I`, the finite source module `M`, the target module `N`, and an
  explicit exponent `m` with `I^[m] N = ⊥`; there is no upstream owner predicate in the chapter
  for this stronger uniform-annihilation hypothesis, so the file should keep it directly rather
  than weaken it to the owner `Module.IsIdealPowerTorsion`;
- derived API: the source-facing existential vanishing statement is the numbered item, while the
  stronger eventual-vanishing statement is a companion obtained from the same factorization proof.

Layer triage:
- `source-facing`: existence of one ideal-power stage where the restriction map
  `Ext^p_A(M, N) → Ext^p_A(I^n M, N)` vanishes when some power of `I` kills `N`;
- `core/canonical`: `idealPowerSubtypeExtPrecomp`;
- `bridge/view`: the factorization theorem
  `exists_ext_factorization_through_ideal_power_target`.
-/

-- Proof sketch: apply Lemma `15.102.2` in positive degree to obtain a constant `c` and a
-- factorization of the restriction map through `Ext^p_A(I^n M, I^(n - c) N)` for all `n ≥ c`.
-- For every `n ≥ c + m`, the target `I^(n - c) N` is zero because `I^[m] N = 0`, so the
-- factorization forces the restriction map to vanish.
/-- Companion to Lemma 15.102.3: if `I^[m]` annihilates `N`, then for every positive degree `p`
the restriction maps `Ext^p_A(M, N) → Ext^p_A(I^n M, N)` are zero for all sufficiently large
`n`. -/
theorem eventually_ext_restriction_zero_of_target_annihilated_by_ideal_power
    (I : Ideal A) (M N : ModuleCat.{u} A) [Module.Finite A M] (p : ℕ) (hp : 0 < p)
    (m : ℕ) (hm : I^[m] N = ⊥) :
    ∃ c : ℕ, ∀ n ≥ c,
      idealPowerSubtypeExtPrecomp I n M N p = 0 := by
  -- The positive-degree factorization from Lemma `15.102.2` is the main source-proof input.
  obtain ⟨c, hc⟩ := exists_ext_factorization_through_ideal_power_target I M N p hp
  refine ⟨c + m, ?_⟩
  intro n hn
  have hc' := hc n (le_trans (Nat.le_add_right c m) hn)
  dsimp only at hc'
  obtain ⟨φ, hφ⟩ := hc'
  have hmc : m ≤ n - c := by
    omega
  -- Once the shifted exponent dominates `m`, the corresponding target stage is already zero.
  have hzeroSub : I^[n - c] N = ⊥ := by
    refine le_antisymm ?_ bot_le
    exact (Submodule.pow_smul_top_le I N hmc).trans (by simp [hm])
  -- Therefore the inclusion `I^[n - c] N ↪ N` is the zero morphism, so postcomposition on `Ext`
  -- vanishes identically.
  have hmk₀ : mk₀ (ModuleCat.ofHom (idealPowerSubtype I (n - c) N)) = 0 := by
    rw [mk₀_eq_zero_iff]
    ext x
    simpa [hzeroSub] using x.2
  have hpost :
      idealPowerSubtypeExtPostcomp I (n - c) (idealPowerStage I n M) N p = 0 := by
    ext x
    rw [idealPowerSubtypeExtPostcomp, hmk₀]
    change x.comp 0 (add_zero p) = 0
    simp
  -- Substitute the factorization and the zero postcomposition map to conclude.
  ext x
  rw [← hφ x, hpost]
  simp

/-- Lemma 15.102.3: if `A` is Noetherian, `M` is a finite `A`-module, and `I^[m]` annihilates
`N`, then for every degree `p > 0` there exists some `n` such that the restriction map
`Ext^p_A(M, N) → Ext^p_A(I^n M, N)` is zero. -/
theorem exists_ext_restriction_zero_of_target_annihilated_by_ideal_power
    (I : Ideal A) (M N : ModuleCat.{u} A) [Module.Finite A M] (p : ℕ) (hp : 0 < p)
    (m : ℕ) (hm : I^[m] N = ⊥) :
    ∃ n : ℕ, idealPowerSubtypeExtPrecomp I n M N p = 0 := by
  -- The companion theorem already gives eventual vanishing, so choose its cutoff.
  obtain ⟨c, hc⟩ :=
    eventually_ext_restriction_zero_of_target_annihilated_by_ideal_power I M N p hp m hm
  exact ⟨c, hc c le_rfl⟩

end
