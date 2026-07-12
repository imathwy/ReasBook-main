import Mathlib
import StacksProject_2024.Chap15.Definition_15_89_1

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

section

open scoped IdealPowerTorsion

variable {R : Type u} [CommRing R]
variable {M : Type v} [AddCommGroup M] [Module R M]
variable {I : Ideal R}

/-
Domain-style sampling pass for Lemma 15.89.4.

Primary domain: commutative algebra of ideal-power torsion modules and their extension closure.

Sampled same-domain owners:
* `Module.IsIdealPowerTorsion` and `Module.isIdealPowerTorsion_iff` from
  `Definition_15_89_1.lean`;
* the source-facing finite-stage owner notation `M[I^n]`, implemented by `Ideal.powerTorsion`;
* `Ideal.primaryComponent` as the canonical owner of `M[I^∞]`;
* the Chapter `15` finite-stage vanishing API from `Lemma_15_89_3.lean`.

Best owner abstraction:
* `source-facing`: the quotient by `M[I^∞]` has no residual `I`-torsion, and ideal-power torsion
  is closed under extensions;
* `core/canonical`: `Module.IsIdealPowerTorsion`, `Ideal.primaryComponent`, and `Ideal.powerTorsion`;
* `bridge/view`: the first clause is the finite-stage vanishing statement for the quotient module,
  written through the chapter owner notation `Q[I^1] = ⊥` rather than the raw
  `Submodule.torsionBySet` expansion.

Primitive data are only the ideal `I`, the module `M`, and in part `(2)` the chosen submodule
`N`. The quotient `M ⧸ M[I^∞]` and its stage-one power-torsion submodule are derived API.
-/

-- Proof sketch: choose finitely many generators of `I`. If the class of `m` in the quotient is
-- `I`-torsion, then each generator sends `m` into the `I`-primary component, hence into some
-- `I^n`-torsion submodule. A sufficiently large power of `I` therefore kills `m`, so its class in
-- the quotient is already zero.
/-- Lemma 15.89.4 (1): if `I` is finitely generated, then the quotient of `M` by its canonical
`I^∞`-torsion submodule `M[I^∞]` has no `I`-torsion. -/
theorem powerTorsion_quotient_primaryComponent_eq_bot
    (hI : I.FG) :
    (((M ⧸ (M[I^∞] : Submodule R M))[I^1]) :
      Submodule R (M ⧸ (M[I^∞] : Submodule R M))) = ⊥ := sorry

-- Proof sketch: let `m : M`. Since `M ⧸ N` is `I`-power torsion, some power of `I` kills the
-- image of `m` in the quotient, so a corresponding power sends `m` into `N`. Since `N` is
-- `I`-power torsion, a further power kills that element of `N`, and therefore a larger power of
-- `I` kills `m`.
/-- Lemma 15.89.4 (2): a module is `I`-power torsion whenever a submodule and the corresponding
quotient are both `I`-power torsion. -/
theorem isIdealPowerTorsion_of_submodule_and_quotient (N : Submodule R M)
    (hN : Module.IsIdealPowerTorsion I N)
    (hQ : Module.IsIdealPowerTorsion I (M ⧸ N)) :
    Module.IsIdealPowerTorsion I M := sorry

end
