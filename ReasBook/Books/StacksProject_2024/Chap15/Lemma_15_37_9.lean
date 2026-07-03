import Mathlib
import StacksProject_2024.Chap15.Definition_15_37_3

-- Declarations for this item will be appended below by the statement pipeline.

open scoped TensorProduct

universe u v w

namespace RingHom

section

open Algebra.TensorProduct

variable {R : Type u} {S : Type v} {R' : Type w}
variable [CommRing R] [CommRing S] [CommRing R']
variable [Algebra R S] [Algebra R R']

/- Domain-style sampling for Lemma 15.37.9:
- primary domain: descent of adic topological formal smoothness along a split base change in
  commutative algebra.
- inspected owner declarations:
  * `RingHom.FormallySmoothTopologically`, the core topological lifting owner from Definition
    `15.37.1`;
  * `RingHom.formally_smooth_for_adic`, the chapter owner bridge for the discrete-source adic
    specialization from Definition `15.37.3`;
  * `RingHom.formally_smooth_for_adic_baseChange`, the forward base-change theorem from
    Lemma `15.37.8`;
  * `RingHom.formallySmoothTopologically_adicSource_iff_discreteSource`, the source-topology bridge
    from Lemma `15.37.2`.
- best owner abstraction: the source-facing theorem in this file should use the chapter adic owner
  `RingHom.formally_smooth_for_adic`; the lower-level owner
  `RingHom.FormallySmoothTopologically` is the core/canonical implementation layer.
- primitive data: the ideal `𝔫 : Ideal S`, the split `R`-linear retraction of `R → R'`, and
  formal smoothness for the base-changed map with respect to the extended ideal.
- derived API: descent of formal smoothness for the original map `R → S`.

Source/core/bridge triage:
- `source-facing`: formal smoothness of `R → S` for the `𝔫`-adic topology.
- `core/canonical`: `RingHom.FormallySmoothTopologically`.
- `bridge/view`: `RingHom.formally_smooth_for_adic`. -/

-- Proof sketch: given a square-zero lifting problem for `R → S`, base change it along `R → R'`
-- to a lifting problem for `R' → R' ⊗[R] S`. The assumed topological formal smoothness over `R'`
-- gives a lift after base change. Choose an `R`-linear retraction `R' → R`, use it to split
-- `A ⊗[R] R'` as `A ⊕ (A ⊗[R] C)`, and then project the lifted map back to the summand `A`,
-- exactly as in the Stacks Project argument.
/-- Lemma 15.37.9: if `R` is an `R`-linear direct summand of `R'` and the canonical base-change map
`R' → R' ⊗[R] S` is formally smooth for the adic topology defined by the extended ideal
`𝔫 (R' ⊗[R] S)`, then `R → S` is formally smooth for the `𝔫`-adic topology. -/
theorem formally_smooth_for_adic_of_split_baseChange
    (𝔫 : Ideal S)
    (hsplit : ∃ σ : R' →ₗ[R] R, Function.LeftInverse σ (Algebra.linearMap R R'))
    (hf : formally_smooth_for_adic
      (includeLeftRingHom : R' →+* R' ⊗[R] S) (Ideal.map includeRight.toRingHom 𝔫)) :
    formally_smooth_for_adic (algebraMap R S) 𝔫 := sorry

end

end RingHom
