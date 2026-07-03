import Mathlib
import StacksProject_2024.Chap10.Definition_10_103_1

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

open IsLocalRing

section

variable {R : Type u} {S : Type v}
variable [CommRing R] [CommRing S] [Algebra R S]
variable [IsRegularLocalRing R]
variable [IsLocalRing S] [IsNoetherianRing S]
variable [IsLocalHom (algebraMap R S)]

local notation "ClosedFiber" => Ideal.Fiber (maximalIdeal R) S

/- Domain-style sampling for the miracle-flatness statement:
* primary domain: local commutative algebra of flat local maps from regular local rings with
  Cohen-Macaulay target and a closed-fiber dimension formula;
* sampled owner declarations:
  `Ideal.Fiber`,
  `Module.CohenMacaulay`,
  `flat_of_tor_one_quotient_vanishing_and_flat_mod_ideal`,
  `algebraMap_flat_of_flat_closedFiber_and_flat_over_base`;
* best owner abstraction: the closed fiber should live on the canonical owner
  `ClosedFiber = Ideal.Fiber (maximalIdeal R) S`, while the conclusion belongs on the canonical
  flatness owner `(algebraMap R S).Flat`;
* primitive data: the local map `R → S`, regularity of `R`, the explicit owner hypothesis
  `hCM : Module.CohenMacaulay S S`, and the dimension formula for `S` and the canonical closed
  fiber;
* derived API: the quotient presentation
  `S ⧸ Ideal.map (algebraMap R S) (maximalIdeal R)` of the closed fiber and the flatness
  conclusion for the algebra map.

Source/core/bridge triage:
* `source-facing`: the Stacks miracle-flatness lemma itself;
* `core/canonical`: `Module.CohenMacaulay`, `Ideal.Fiber`, and `(algebraMap R S).Flat`;
* `bridge/view`: the quotient presentation of `ClosedFiber`.
-/

-- Proof sketch: induct on `ringKrullDim R`. For positive dimension, use prime avoidance to choose
-- `x ∈ maximalIdeal R \ maximalIdeal R ^ 2` avoiding the contractions of the minimal primes of
-- `S`; this makes `x` a nonzerodivisor on the Cohen-Macaulay ring `S`. Quotienting by `x` lowers
-- both dimensions by one and preserves regularity of `R / xR` and Cohen-Macaulayness of `S / xS`,
-- so the induction hypothesis gives flatness modulo `x`. Then apply the variant of the local
-- criterion for flatness to lift flatness from the quotient.
/-- Lemma 10.128.1: let `R → S` be a local homomorphism of Noetherian local rings. If `R` is a
regular local ring, `S` is Cohen-Macaulay, and the dimension formula
`dim S = dim R + dim ((maximalIdeal R).Fiber S)`, equivalently
`dim S = dim R + dim (S ⧸ Ideal.map (algebraMap R S) (maximalIdeal R))`, holds, then `R → S` is
flat. -/
theorem algebraMap_flat_of_isRegularLocalRing_of_cohenMacaulay_of_dimension_formula
    (hCM : Module.CohenMacaulay S S)
    (hdim : ringKrullDim S = ringKrullDim R + ringKrullDim ClosedFiber) :
    (algebraMap R S).Flat := sorry

end
