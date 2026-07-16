import Mathlib.Tactic.Recall
import stacks_proof.stacks_project.Chap15.Definition_15_37_3

-- Declarations for this item will be appended below by the statement pipeline.

/- Domain-style sampling for Lemma 15.37.8:
- primary domain: adic topological formal smoothness of commutative ring maps under tensor-product
  base change.
- inspected owner declarations:
  * `RingHom.formally_smooth_for_adic`
  * `RingHom.formally_smooth_for_adic_of_le`
  * `RingHom.FormallySmoothTopologically`
  * `RingHom.FormallySmooth.isStableUnderBaseChange`
- best owner abstraction: the source-facing theorem belongs to the chapter owner
  `RingHom.formally_smooth_for_adic`; the lower-level topological owner and the algebraic
  base-change owner are implementation/core layers.
- primitive data: the ideal `𝔫 : Ideal S`, the adic formal smoothness hypothesis for
  `algebraMap R S`, and the algebra structures needed to form `R' ⊗[R] S`.
- derived API: formal smoothness for the canonical base-change map with respect to the extended
  ideal on the tensor product.
- source/core/bridge triage:
  * `source-facing`: adic formal smoothness of the base-changed map.
  * `core/canonical`: `RingHom.FormallySmoothTopologically` and
    `RingHom.FormallySmooth.isStableUnderBaseChange`.
  * `bridge/view`: `RingHom.formally_smooth_for_adic`. -/

/- Lemma 15.37.8: base change for adic formal smoothness is now owner-level derived API on
`RingHom.formally_smooth_for_adic`, so this file is a direct recall of that theorem. -/
recall RingHom.formally_smooth_for_adic_baseChange
