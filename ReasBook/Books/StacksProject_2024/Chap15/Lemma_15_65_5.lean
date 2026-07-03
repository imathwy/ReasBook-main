import Mathlib
import StacksProject_2024.Chap13.Lemma_13_15_4
import StacksProject_2024.Chap15.Lemma_15_65_3

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open CategoryTheory
open CategoryTheory.Limits

universe u

attribute [local instance] HasDerivedCategory.standard

section

variable {R : Type u} [Ring R]

local notation "Cpx" => CochainComplex (ModuleCat R) ℤ
local notation "FiniteProjectiveClass" => (fun P : ModuleCat R ↦ Module.Finite R P ∧ Projective P)
local notation "FiniteFreeClass" => (fun P : ModuleCat R ↦ Module.Free R P ∧ Module.Finite R P)

/- Domain-style sampling for Lemma 15.65.5:
- primary domain: pseudo-coherence of cochain complexes via bounded-above finite-free and finite-
  projective models;
- sampled owner declarations:
  `DerivedCategory.IsMPseudoCoherent`,
  `DerivedCategory.IsPseudoCoherent`,
  `CochainComplex.IsTermwiseFiniteFree`,
  `CochainComplex.MinusWithTermsIn`;
- best owner abstraction: the pseudo-coherence owners stay `K.IsMPseudoCoherent` and
  `K.IsPseudoCoherent`, while bounded-above model data should be carried by the existing owner
  `CochainComplex.MinusWithTermsIn` specialized to the finite-projective or finite-free term
  class, rather than by a parallel local wrapper that repeats boundedness and termwise membership;
- primitive vs. derived:
  primitive data are a bounded-above owner complex in `MinusWithTermsIn ...` and a quasi-
  isomorphism to the target complex;
  derived API is the TFAE and the bounded-above finite-free existence statement below;
- source/core/bridge triage:
  `source-facing`: the TFAE and the finite-free existence theorem;
  `core/canonical`: `K.IsMPseudoCoherent`, `K.IsPseudoCoherent`, and `MinusWithTermsIn`;
  `bridge/view`: the existential model clauses relating a cochain complex to a chosen owner
    complex in `MinusWithTermsIn`.
-/

-- Proof sketch: `(1) → (3)` is immediate because finite free modules are finite projective. For
-- `(3) → (1)`, replace each finite projective term by a finite free module using a direct-summand
-- argument to obtain a bounded-above finite-free complex that is still quasi-isomorphic to `K`.
-- Then `(1) → (2)` comes from stupid truncations of a bounded-above finite-free model, while
-- `(2) → (3)` is built by the descending-induction argument of the Stacks proof, using Lemmas
-- `15.65.2` and `15.65.3` to keep control of pseudo-coherence and finiteness at each step.
/-- Lemma 15.65.5: for a cochain complex `K^•` of `R`-modules, the following are equivalent:
`K^•` is pseudo-coherent, `K^•` is `m`-pseudo-coherent for every `m : ℤ`, and `K^•` is
quasi-isomorphic to a bounded-above cochain complex of finite projective `R`-modules. -/
theorem cochainComplex_pseudoCoherent_tfae
    (K : Cpx) :
    [K.IsPseudoCoherent,
      ∀ m : ℤ, K.IsMPseudoCoherent m,
      ∃ P : CochainComplex.MinusWithTermsIn FiniteProjectiveClass,
        ∃ α : (P : Cpx) ⟶ K, QuasiIso α].TFAE := sorry

-- Proof sketch: start from a bounded-above finite-free model of `K` given by pseudo-coherence and
-- descend from degree `b + 1`, extending the partial finite-free approximation one step at a time.
-- The cone of the partial map stays `(n - 1)`-pseudo-coherent by Lemma `15.65.2`, Lemma `15.65.3`
-- makes the relevant cohomology finite, and adjoining finitely many free generators yields the
-- next stage while keeping the complex zero above degree `b`.
/-- A pseudo-coherent cochain complex with vanishing cohomology above `b` admits a
quasi-isomorphic bounded-above termwise finite-free model concentrated in degrees `≤ b`. -/
theorem exists_boundedAbove_termwiseFiniteFree_quasiIso
    {K : Cpx} {b : ℤ}
    (hK : K.IsPseudoCoherent)
    (hvanish : ∀ i : ℤ, b < i → IsZero (K.homology i)) :
    ∃ F : CochainComplex.MinusWithTermsIn FiniteFreeClass,
      (F : Cpx).IsStrictlyLE b ∧
        ∃ α : (F : Cpx) ⟶ K, QuasiIso α := sorry

end
end
