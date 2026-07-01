import Mathlib.Data.List.TFAE
import Mathlib.Tactic.TFAE
import stacks_project.Chap10.Lemma_10_39_5
import stacks_project.Chap10.Remark_10_75_9

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory CategoryTheory.Limits Equiv
open scoped TensorProduct

universe u

section

variable {R : Type u} [CommRing R]
variable {M : Type u} [AddCommGroup M] [Module R M]

set_option quotPrecheck false in
local notation "Tor[" i "](" N ")" => (((Tor (ModuleCat R) i).obj (ModuleCat.of R M)).obj N)
set_option quotPrecheck false in
local notation "Tor₁(" N ")" => Tor[1](N)
set_option quotPrecheck false in
local notation "Tor₁[" R "](" N ")" => Tor[1](ModuleCat.of R N)

/- Domain triage:
- primary domain: commutative algebra of flat modules and Tor-vanishing criteria;
- sampled owner declarations of the same kind:
  `Module.Flat`,
  `Module.Flat.iff_rTensor_injective'`,
  `Module.Flat.iff_lift_lsmul_comp_subtype_injective`,
  `tor_one_quotient_by_ideal_equiv_ker_ideal_tensor_to_module`;
- best owner abstraction: the canonical owner is `Module.Flat`, with the chapter-local Tor/kernel
  bridge supplying the quotient-by-ideal reformulations;
- primitive data: the commutative ring `R` and the `R`-module `M`;
- derived API: the five-way `List.TFAE` packaging of flatness, higher Tor-vanishing, and the two
  quotient-ideal tests.

Source/core/bridge triage:
- `source-facing`: the Stacks-style five-way flatness criterion recorded as a `TFAE`;
- `core/canonical`: `Module.Flat` and the owner theorems `Module.Flat.iff_rTensor_injective'` and
  `Module.Flat.iff_lift_lsmul_comp_subtype_injective`;
- `bridge/view`: `tor_one_quotient_by_ideal_equiv_ker_ideal_tensor_to_module`, which converts the
  quotient-side `Tor₁` condition to the canonical tensor-kernel test.
-/

-- Proof sketch: use the derived-functor definition of `Tor`. If `M` is flat, then tensoring with
-- `M` is exact, so all higher left-derived functors vanish. The implications from vanishing for all
-- `i > 0` to the special `Tor₁` vanishing conditions are immediate. For the converse, apply the
-- six-term exact sequence of Lemma `10.75.2` to `0 → I → R → R/I → 0`; vanishing of
-- `Tor₁^R(M, R/I)` makes `I ⊗[R] M → M` injective, and Lemma `10.39.5` then yields flatness.
/-- Lemma 10.75.8: for an `R`-module `M`, the following are equivalent: `M` is flat over `R`; all
higher functors `Tor_i^R(M, -)` for `i > 0` vanish; `Tor_1^R(M, -)` vanishes; `Tor_1^R(M, R/I)`
vanishes for every ideal `I`; and it suffices to check this for finitely generated ideals `I`. -/
theorem flat_tfae_tor_vanishing_criteria :
    List.TFAE
      [ Module.Flat R M,
        ∀ i : ℕ, 0 < i → ∀ N : ModuleCat R,
          IsZero (Tor[i](N)),
        ∀ N : ModuleCat R, IsZero (Tor₁(N)),
        ∀ I : Ideal R,
          IsZero (Tor₁[R](R ⧸ I)),
        ∀ I : Ideal R, I.FG →
          IsZero (Tor₁[R](R ⧸ I)) ] := by
  tfae_have 1 → 2 := by
    intro hflat i hi N
    sorry
  tfae_have 2 → 3 := by
    intro h N
    simpa using h 1 (Nat.succ_pos 0) N
  tfae_have 3 → 4 := by
    intro h I
    simpa using h (ModuleCat.of R (R ⧸ I))
  tfae_have 4 → 5 := by
    intro h I _
    exact h I
  tfae_have 5 → 1 := by
    intro hTor
    rw [Module.Flat.iff_lift_lsmul_comp_subtype_injective]
    intro I hI
    let μ :
        I ⊗[R] M →ₗ[R] M :=
      TensorProduct.lift ((LinearMap.lsmul R M).comp I.subtype)
    have htor :
        Tor₁[R](R ⧸ I) ≃ₗ[R] LinearMap.ker μ :=
      tor_one_quotient_by_ideal_equiv_ker_ideal_tensor_to_module I
    have hker_subsingleton : Subsingleton (LinearMap.ker μ) := by
      exact (subsingleton_congr htor.toEquiv).mp
        ((ModuleCat.isZero_iff_subsingleton).1 (hTor I hI))
    exact LinearMap.ker_eq_bot.mp <| Submodule.subsingleton_iff_eq_bot.mp hker_subsingleton
  tfae_finish

end
