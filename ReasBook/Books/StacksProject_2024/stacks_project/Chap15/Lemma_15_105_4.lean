import Mathlib
import StacksProject_2024.Chap15.Definition_15_105_1
import StacksProject_2024.Chap15.Definition_15_105_3

open CategoryTheory
open scoped TensorProduct

-- Declarations for this item will be appended below by the statement pipeline.

universe u v w

noncomputable section

section

variable (A : Type u) [CommRing A]
variable (B : Type v) [CommRing B] [Algebra A B]
variable (d : ℕ) [HasWeakDimensionLE A d]

/- Domain triage:
- primary domain: weak dimension of commutative rings and its behavior under weakly étale maps;
- sampled owner declarations:
  `HasWeakDimensionLE`,
  `ModuleHasTorDimensionLE`,
  `ModuleCat.hasTorDimensionLE_iff_hasFiniteFlatResolutionLengthLE`,
  `Algebra.IsWeaklyEtale`;
- best owner abstraction: the ring-level owner is `HasWeakDimensionLE`, with the explicit owner
  input `hAB : Algebra.IsWeaklyEtale A B` supplying the flatness input on the structure map and
  tensor-square multiplication;
- primitive vs. derived:
  the primitive data live in the owner classes `HasWeakDimensionLE A d` and
  `Algebra.IsWeaklyEtale A B`;
  the source-facing transfer theorem below and the resulting owner instance on `B` are derived API.

Source/core/bridge triage:
- `source-facing`: `hasWeakDimensionLE_of_isWeaklyEtale`;
- `core/canonical`: `HasWeakDimensionLE` and `Algebra.IsWeaklyEtale`;
- `bridge/view`: the tor-dimension/flat-resolution comparison from Lemma `15.67.6`, together with
  base change of flat modules along a flat algebra map.
-/

-- Proof sketch: for `N : ModuleCat B`, first forget to an `A`-module. The weak-dimension owner on
-- `A` supplies a finite flat `A`-resolution of length `d`. Because a weakly étale map is flat,
-- tensoring that resolution with `B` over `A` preserves exactness, and each flat `A`-module
-- stays flat after base change to `B`. Finally, `B ⊗[A] N ≅ N`, so the tensorized resolution is a
-- finite flat `B`-resolution of `N`.
/-- Helper for Lemma 15.105.4: base changing a `B`-module from `A` back to `B` recovers the same
`B`-module. -/
private noncomputable def baseChange_cancel (N : ModuleCat.{w} B) :
    let _ : Module A (N : Type w) := Module.compHom (N : Type w) (algebraMap A B)
    B ⊗[A] (N : Type w) ≃ₗ[B] (N : Type w) :=
  let _ : Module A (N : Type w) := Module.compHom (N : Type w) (algebraMap A B)
  let _ : IsScalarTower A B (N : Type w) := RestrictScalars.isScalarTower A B (N : Type w)
  TensorProduct.lidOfCompatibleSMul A B (N : Type w)

/-- Helper for Lemma 15.105.4: composing the right map of an exact pair with a linear equivalence
preserves exactness. -/
private lemma exact_comp_linearEquiv
    {R : Type*} [CommRing R]
    {M N P Q : Type*}
    [AddCommGroup M] [AddCommGroup N] [AddCommGroup P] [AddCommGroup Q]
    [Module R M] [Module R N] [Module R P] [Module R Q]
    {f : M →ₗ[R] N} {g : N →ₗ[R] P}
    (hfg : Function.Exact f g) (e : P ≃ₗ[R] Q) :
    Function.Exact f (e.toLinearMap.comp g) := by
  sorry

/-- Helper for Lemma 15.105.4: base change of a finite flat `A`-resolution along a flat map
`A → B` yields a finite flat `B`-resolution. -/
private lemma finiteFlatResolution_baseChange
    [Module.Flat A B]
    (N : ModuleCat B) {d : ℕ}
    (hN :
      ModuleCat.HasFiniteFlatResolutionLengthLE
        ((ModuleCat.restrictScalars (algebraMap A B)).obj N) d) :
    ModuleCat.HasFiniteFlatResolutionLengthLE N d := by
  sorry

/-- Lemma 15.105.4: if `A → B` is weakly étale and `A` has weak dimension at most `d`, then `B`
has weak dimension at most `d`. -/
theorem hasWeakDimensionLE_of_isWeaklyEtale
    (hAB : Algebra.IsWeaklyEtale A B) :
    HasWeakDimensionLE B d := by
  sorry

-- This transfer is intentionally not registered as a global instance. Unlike base change in
-- Lemma `15.105.7`, the source ring `A` of a weakly étale map `A → B` is not determined by the
-- target owner `HasWeakDimensionLE B d`, so typeclass search would have to guess a noncanonical
-- ambient algebra `A → B`.

end
