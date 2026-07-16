import Mathlib.RingTheory.AdicCompletion.Basic
import Mathlib.RingTheory.Noetherian.Basic
import stacks_proof.stacks_project.Chap10.Definition_10_5_1
import stacks_proof.stacks_project.Chap10.Lemma_10_51_2_Artin_Rees
import stacks_proof.stacks_project.Chap10.Remark_10_75_9
import stacks_proof.stacks_project.Chap12.Definition_12_31_2
import stacks_proof.stacks_project.Chap15.Definition_15_61_1
import Mathlib.Tactic.StacksAttribute

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open CategoryTheory ModuleCat AdicCompletion

universe u

section

variable {A : Type u} [CommRing A]
variable (I : Ideal A)
variable {M : Type u} [AddCommGroup M] [Module A M]

/-- The inverse system `(Tor_p^A(M, A ⧸ I^n))_n` attached to the ideal-power quotients of `A`.
Since `I ^ 0 = ⊤`, stage `0` is the zero Tor object. -/
abbrev idealPowerQuotientTorInverseSystem (I : Ideal A) (M : Type u) [AddCommGroup M]
    [Module A M] (p : ℕ) : SequentialInverseSystem (ModuleCat A) :=
  let X : ℕ → ModuleCat A := fun n ↦ Tor[A, p](M, A ⧸ I ^ n • (⊤ : Submodule A A))
  let f : ∀ n : ℕ, X (n + 1) ⟶ X n := fun n ↦
    ((Tor (ModuleCat A) p).obj (of A M)).map <| ofHom <| transitionMap I A (Nat.le_succ n)
  Functor.ofOpSequence f

end

section

variable {A : Type u} [CommRing A] [IsNoetherianRing A]
variable (I : Ideal A)
variable {M : Type u} [AddCommGroup M] [Module A M] [Module.Finite A M]

-- Proof sketch: present `M` by a finite free module, identify `Tor_1^A(M, A/I^n)` with
-- `(K ∩ I^n F) / I^n K`, apply Artin-Rees to make the transition map vanish for `p = 1`, and then
-- deduce the higher-degree case by dimension shifting along the presentation.
/-- Lemma 15.27.3: over a Noetherian ring, for every `p > 0` there is `c` such that the map
on `Tor_p^A(M, A ⧸ I^n)` induced by `A ⧸ I^n → A ⧸ I^(n - c)` is zero for all `n ≥ c`. -/
@[stacks 0911]
theorem tor_eventually_zero_map_quotient_pow (p : ℕ) (hp : 0 < p) :
    ∃ c : ℕ, ∀ n ≥ c,
      (idealPowerQuotientTorInverseSystem I M p).transitionMap (Nat.sub_le n c) = 0 := by
  sorry

end
