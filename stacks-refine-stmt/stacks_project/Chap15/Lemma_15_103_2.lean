import Mathlib
import stacks_project.Chap15.Lemma_15_102_1

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open CategoryTheory

universe u

namespace CategoryTheory

section

variable {A : Type u} [CommRing A] [IsNoetherianRing A]

/- Domain-style sampling for Lemma 15.103.2:
- primary domain: Tor functoriality for the inclusion `I^[n] M ↪ M` of ideal-power submodules of a
  finite module over a Noetherian ring;
- sampled owner declarations:
  `Tor[A, p](X, Y)`,
  `idealPowerSubtype`,
  `idealPowerSubtypeTorMap`,
  `exists_idealPower_inclusion_factorization_through_ideal_derivedTensor_map`;
- best owner abstraction: the source-facing theorem should use the chapter owner
  `idealPowerSubtypeTorMap` for the induced map
  `Tor_p^A(I^[n] M, N) → Tor_p^A(M, N)`, while the factorization through the derived tensor map
  from Lemma `15.102.7` remains proof-level bridge data;
- primitive data: the ideal `I`, the finite module `M`, the target module `N`, and the
  annihilator containment `I ≤ Module.annihilator A N`;
- derived API: the existential vanishing statement below for the canonical Tor map
  `idealPowerSubtypeTorMap`.

Source/core/bridge triage:
- `source-facing`: existence of an ideal-power stage where the canonical map on all Tor groups
  vanishes;
- `core/canonical`: `Tor[A, p](X, Y)` and `idealPowerSubtypeTorMap`;
- `bridge/view`: the derived-tensor factorization from Lemma `15.102.7`. -/

-- Proof sketch: apply Lemma `15.102.7` to factor the inclusion `I^[n] M → M` through the derived
-- tensor map induced by `I → A`, then tensor with `N`. Since `I ≤ Module.annihilator A N`, the
-- map `I ⊗_A^{\mathbf L} N → N` is zero, so the induced maps on all Tor groups vanish.
/-- Lemma 15.103.2: if `A` is Noetherian, `I ⊆ A` is an ideal, `M` is a finite `A`-module, and
`N` is annihilated by `I`, then some positive power `I^n M` maps trivially to `M` on every
`Tor_p^A(-, N)`. -/
theorem exists_idealPower_tor_map_eq_zero_of_annihilator_le
    (I : Ideal A) (M N : ModuleCat A) [Module.Finite A M]
    (hN : I ≤ Module.annihilator A N) :
    ∃ n : ℕ, 0 < n ∧ ∀ p : ℕ,
      idealPowerSubtypeTorMap I n M N p = 0 := sorry

end

end CategoryTheory
