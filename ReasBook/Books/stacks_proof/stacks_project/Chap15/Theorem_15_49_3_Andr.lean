import Mathlib.Data.List.TFAE
import StacksProject_2024.Chap15.Definition_15_37_3
import StacksProject_2024.Chap15.Definition_15_41_1
import Mathlib.Tactic.StacksAttribute

-- Declarations for this item will be appended below by the statement pipeline.

attribute [local instance] Algebra.TensorProduct.rightAlgebra

open IsLocalRing
open scoped TensorProduct

universe u v

section

variable {A : Type u} {B : Type v} [CommRing A] [CommRing B] [Algebra A B]
variable [IsLocalRing A] [IsLocalRing B] [IsNoetherianRing A] [IsNoetherianRing B]
variable [IsLocalHom (algebraMap A B)]

local notation "ClosedFiber" => Ideal.Fiber (maximalIdeal A) B
local notation "𝔪ClosedFiber" => Ideal.map (algebraMap B ClosedFiber) (maximalIdeal B)

/- Domain-style sampling for Theorem 15.49.3 (André):
- primary domain: regular local morphisms of Noetherian local rings, their special fibers, and
  adic formal smoothness;
- sampled owner declarations:
  `RingHom.IsRegularRingMap`,
  `flat_geometricallyRegularSpecialFiber_formallySmooth_tfae`,
  `RingHom.formally_smooth_for_adic_tfae_completion_invariance`,
  `RingHom.IsRegularRingMap.of_comp_of_faithfullyFlat`;
- best owner abstraction: this theorem is `source-facing`; its main clause is the canonical owner
  `(algebraMap A B).IsRegularRingMap`, while the remaining three clauses should reuse the
  already-established
  special-fiber owner package from Proposition `15.40.5` rather than introducing any parallel
  local wrapper;
- primitive data: the local map `algebraMap A B`, the closed fiber `ClosedFiber`, the adic ideal
  `𝔪ClosedFiber`, and the regularity hypothesis on the completion map `A → A^∧`;
- derived API: the equivalence among the last three clauses from Proposition `15.40.5`, and the
  completion/descent bridge used to compare clause `(1)` with that owner package.

Source/core/bridge triage:
- `source-facing`: the four-way `List.TFAE` theorem below;
- `core/canonical`: `(algebraMap A B).IsRegularRingMap`, `Ideal.Fiber`, and
  `RingHom.formally_smooth_for_adic`;
- `bridge/view`: the tensor-product presentation `ResidueField A ⊗[A] B` of `ClosedFiber` and the
  completion maps entering the André hypothesis.
-/

-- Proof sketch: Proposition `15.40.5` gives the equivalence of the last three clauses. The
-- implication from regularity to flatness plus geometric regularity of the special fiber is the
-- closed-fiber part of the definition of `(algebraMap A B).IsRegularRingMap`. For the
-- converse, apply
-- Lemma `15.37.4` to pass formal smoothness to completions, use Proposition `15.49.2` to deduce
-- that `A^∧ → B^∧` is regular, compose with the assumed regular map `A → A^∧`, and then descend
-- regularity across the faithfully flat completion map `B → B^∧` by Lemma `15.41.7`.
/-- Theorem 15.49.3 (André): let `A → B` be a local homomorphism of Noetherian local rings, let
`ClosedFiber = Ideal.Fiber (maximalIdeal A) B`, canonically presented by
`ResidueField A ⊗[A] B`, be the special fiber. If the completion map
`A → AdicCompletion (maximalIdeal A) A` is regular, then the regularity of `A → B`, the standard
flatness-plus-closed-fiber conditions, and adic formal smoothness of `A → B` are equivalent. -/
@[stacks 0H7U]
theorem regularRingMap_specialFiber_formallySmooth_tfae_of_regular_completion
    (hA_completion :
      (algebraMap A (AdicCompletion (maximalIdeal A) A)).IsRegularRingMap) :
    List.TFAE [
      (algebraMap A B).IsRegularRingMap,
      (algebraMap A B).Flat ∧ Algebra.IsGeometricallyRegular (ResidueField A) ClosedFiber,
      (algebraMap A B).Flat ∧
        (algebraMap (ResidueField A) ClosedFiber).formally_smooth_for_adic 𝔪ClosedFiber,
      (algebraMap A B).formally_smooth_for_adic (maximalIdeal B)
    ] := sorry

end
