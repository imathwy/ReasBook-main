import StacksProject_2024.Chap15.Lemma_15_102_Basic

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

attribute [local instance] CategoryTheory.HasExt.standard

open CategoryTheory.Abelian
open CategoryTheory.Abelian.Ext
open scoped IdealPowerSubmodule

universe u

section

variable {A : Type u} [CommRing A] [IsNoetherianRing A]
variable (I : Ideal A) (M N : ModuleCat A) [Module.Finite A M]

local notation "Mod" => ModuleCat A

/- Domain-style sampling:
- primary domain: Ext-groups of finite modules over a Noetherian ring, with restriction maps
  induced by the inclusions `I^[n] M ↪ M` and `I^[n - c] N ↪ N`;
- sampled owner declarations:
  `idealPowerSubtype`,
  `idealPowerSubtypeExtPrecomp`,
  `idealPowerSubtypeExtPostcomp`;
- best owner abstraction: the chapter owner surface for these restriction maps is
  `idealPowerSubtypeExtPrecomp` in the source variable and `idealPowerSubtypeExtPostcomp` in the
  target variable, both derived canonically from `idealPowerSubtype`;
- primitive data: the ideal `I`, the finite source module `M`, the target module `N`, the degree
  `p`, and the ideal-power inclusions on `M` and `N`;
- derived API: the eventual factorization of the restriction map through
  `Ext^p_A(I^[n] M, I^[n - c] N)`.

Layer triage:
- `source-facing`: the eventual factorization statement from the Stacks lemma;
- `core/canonical`: `idealPowerSubtype`, `Ext.precompOfLinear`, and `Ext.postcompOfLinear`;
- `bridge/view`: the witness map `φ` giving the factorization through the ideal-power target. -/

-- Proof sketch: the source lemma is the positive-degree statement. In degree `0`, the
-- restriction map already factors with `c = 0` by viewing a morphism `M ⟶ N` as a morphism
-- `I^n M ⟶ I^n N`. For `p > 0`, apply Artin-Rees to a finite presentation of `M` to obtain a
-- uniform constant `c`; for each `n ≥ c`, the induced map on a free resolution of `I^n M` lands
-- in `I^(n - c) N`, which yields the required factorization on `Ext^p` by induction on `p`.
/-- Lemma 15.102.2: for every degree `p > 0`, the canonical `A`-linear restriction map
`Ext^p_A(M, N) → Ext^p_A(I^n M, N)` factors for large `n` through some `A`-linear map
`Ext^p_A(M, N) → Ext^p_A(I^n M, I^(n - c) N)`, whose postcomposition with the canonical map
`Ext^p_A(I^n M, I^(n - c) N) → Ext^p_A(I^n M, N)` induced by `I^(n - c) N ↪ N` recovers the
restriction map. -/
theorem exists_ext_factorization_through_ideal_power_target (p : ℕ) (hp : 0 < p) :
    ∃ c : ℕ, ∀ n ≥ c,
      let Mn := idealPowerStage I n M
      let Nn := idealPowerStage I (n - c) N
      ∃ φ :
        Ext M N p →ₗ[A] Ext Mn Nn p,
        ∀ x : Ext M N p,
          idealPowerSubtypeExtPostcomp I (n - c) Mn N p (φ x) =
            idealPowerSubtypeExtPrecomp I n M N p x :=
  sorry

end
