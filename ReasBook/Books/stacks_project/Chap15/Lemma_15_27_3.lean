import Mathlib.RingTheory.AdicCompletion.Basic
import Mathlib.RingTheory.Noetherian.Basic
import stacks_project.Chap12.Definition_12_31_2
import stacks_project.Chap15.Definition_15_61_1

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open CategoryTheory ModuleCat AdicCompletion

universe u

section

variable {A : Type u} [CommRing A] [IsNoetherianRing A]
variable (I : Ideal A)
variable {M : Type u} [AddCommGroup M] [Module A M]

/- Domain-style sampling for the Artin-Rees vanishing statement on Tor:
- primary domain: commutative algebra and homological algebra of the Tor tower
  `Tor_p^A(M, A / I^n)` over ideal-power quotients;
- sampled owner declarations of the same kind:
  `Tor[A, p](M, N)`,
  `AdicCompletion.transitionMap`,
  `CategoryTheory.SequentialInverseSystem.transitionMap`,
  `Functor.ofOpSequence`;
- best owner abstraction: the source-facing theorem should use the canonical Tor tower as a
  `SequentialInverseSystem (ModuleCat A)`, with transition maps derived from the owner API
  `SequentialInverseSystem.transitionMap`; the Artin-Rees argument is proof-level and should not
  appear as extra public data;
- primitive data: the ideal `I`, the finite `A`-module `M`, and the positive degree `p`;
- derived API: the quotient-power Tor inverse system and the eventual vanishing theorem for its
  canonical transition morphisms; the associated inverse system should be assembled directly with
  `Functor.ofOpSequence`.

Source/core/bridge triage:
- `source-facing`: the eventual vanishing statement for
  `Tor_p^A(M, A / I^n) ⟶ Tor_p^A(M, A / I^(n - c))`;
- `core/canonical`: `Tor[A, p](M, N)`, `SequentialInverseSystem.transitionMap`, and
  `Functor.ofOpSequence`;
- `bridge/view`: the quotient transition morphisms `A ⧸ I^(n + 1) → A ⧸ I^n`, pushed through the
  canonical functor `Tor[A, p](M, -)` and assembled by `Functor.ofOpSequence`; the only public
  derived owner remains the resulting inverse system.
-/

/-- The inverse system `(Tor_p^A(M, A ⧸ I^n))_n` attached to the ideal-power quotients of `A`.
Since `I ^ 0 = ⊤`, stage `0` is the zero Tor object. -/
abbrev idealPowerQuotientTorInverseSystem (I : Ideal A) (M : Type u) [AddCommGroup M]
    [Module A M] (p : ℕ) : SequentialInverseSystem (ModuleCat A) :=
  let X : ℕ → ModuleCat A := fun n ↦ Tor[A, p](M, A ⧸ I ^ n • (⊤ : Submodule A A))
  let f : ∀ n : ℕ, X (n + 1) ⟶ X n := fun n ↦
    ((Tor (ModuleCat A) p).obj (of A M)).map <| ofHom <| transitionMap I A (Nat.le_succ n)
  Functor.ofOpSequence f

variable [Module.Finite A M]

-- Proof sketch: present `M` by a finite free module, identify `Tor_1^A(M, A/I^n)` with
-- `(K ∩ I^n F) / I^n K`, apply Artin-Rees to make the transition map vanish for `p = 1`, and then
-- deduce the higher-degree case by dimension shifting along the presentation.
/-- Lemma 15.27.3: over a Noetherian ring, for every `p > 0` there is `c` such that the map
on `Tor_p^A(M, A ⧸ I^n)` induced by `A ⧸ I^n → A ⧸ I^(n - c)` is zero for all `n ≥ c`. -/
theorem tor_eventually_zero_map_quotient_pow (p : ℕ) (hp : 0 < p) :
    ∃ c : ℕ, ∀ n ≥ c,
      (idealPowerQuotientTorInverseSystem I M p).transitionMap (Nat.sub_le n c) = 0 := sorry

end
