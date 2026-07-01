import Mathlib
import stacks_project.Chap15.Definition_15_84_1
import stacks_project.Chap15.Lemma_15_67_20
import stacks_project.Chap15.Lemma_15_76_4

noncomputable section

open CategoryTheory
open scoped TensorProduct DerivedTensorWithAlgebra

universe u

attribute [local instance] HasDerivedCategory.standard
attribute [local instance] Algebra.TensorProduct.leftAlgebra
attribute [local instance] Algebra.TensorProduct.rightAlgebra

namespace CategoryTheory

section

variable {R' A' R : Type u} [CommRing R'] [CommRing A'] [CommRing R]
variable [Algebra R' A'] [Algebra R' R]
variable [Module.Flat R' A']

local notation "A" => A' ⊗[R'] R
local notation "DModA'" => DerivedCategory (ModuleCat A')

/- Domain-style sampling for Lemma 15.84.8:
- primary domain: descent of relative perfectness in derived categories of module categories across
  a nilpotent thickening of the base ring;
- sampled owner declarations:
  `DerivedCategory.IsPerfectOver`,
  `derivedTensorBaseChange`,
  `isPseudoCoherent_derivedTensorWithAlgebra_iff_of_surjective_of_nilpotent_ker`,
  `hasTorAmplitudeIn_derivedTensorWithAlgebra_iff_of_surjective_of_nilpotent_ker`;
- best owner abstraction: the source-facing statement belongs on the chapter owner predicate
  `DerivedCategory.IsPerfectOver`, while the comparison between restriction of
  `K' ⊗[A']^L[A]` to `R` and base change of `K'` restricted to `R'` is a bridge/view supplied by
  `derivedTensorBaseChange`;
- primitive vs. derived:
  primitive data are the flat algebra map `R' → A'`, the nilpotent thickening `R' → R`, and the
  object `K' : D(A')`;
  pseudo-coherence descent, tor-amplitude descent, and the base-change comparison are derived API
  over those owners;
- source/core/bridge triage:
  `source-facing`: descent of `DerivedCategory.IsPerfectOver` across `R' → R`;
  `core/canonical`: `DerivedCategory.IsPerfectOver`, `HasFiniteTorDimension`, and the nilpotent
    descent theorems for pseudo-coherence and tor amplitude;
  `bridge/view`: `derivedTensorBaseChange` and its Tor-independent isomorphism from
    `Lemma_15_61_2`.
-/

-- Proof sketch: unfold `DerivedCategory.IsPerfectOver`. Pseudo-coherence descends directly by
-- Lemma `15.76.4`. For finite tor dimension over the base, use the Tor-independent base-change
-- comparison from Lemma `15.61.2` to identify the restricted object
-- `(K' ⊗[A']^L[A])|_R` with the derived base change of `K'|_{R'}` to `R`, where Tor
-- independence comes from the flatness of `A'` over `R'`; then apply Lemma `15.67.20` across the
-- surjection `R' → R`. The source also assumes that `R' → A'` is of finite presentation, but
-- that hypothesis is redundant for this descent step.
/-- Lemma 15.84.8: let `R' → A'` be a flat ring map, let `R' → R` be a surjective ring map with
nilpotent kernel, and set `A = A' ⊗[R'] R`. If the derived base change
`K' \otimes_{A'}^{\mathbf L} A` is perfect relative to `R`, then `K'` is perfect relative to
`R'`. The finite-presentation hypothesis on `R' → A'` from the source is not needed here. -/
theorem isPerfectOver_of_derivedTensorWithAlgebra_of_surjective_of_nilpotent_ker
    (hsurj : Function.Surjective (algebraMap R' R))
    (hker : IsNilpotent (RingHom.ker (algebraMap R' R)))
    {K' : DModA'}
    (hK :
      DerivedCategory.IsPerfectOver R (K' ⊗[A']^L[A])) :
    DerivedCategory.IsPerfectOver R' K' := by
  sorry

end

end CategoryTheory
