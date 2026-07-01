import Mathlib
import stacks_project.Chap15.Lemma_15_91_6

-- Declarations for this item will be appended below by the statement pipeline.

open scoped TensorProduct

noncomputable section

universe u w

section

variable {R : Type u} [CommRing R]
variable {R' : Type u} [CommRing R'] [Algebra R R']
variable {M : Type w} [AddCommMonoid M] [Module R M]
local notation "Away" => LocalizedModule.Away

/- Domain-style sampling:
* primary domain: Beauville-Laszlo glueing pairs and flatness descent for a single localization.
* sampled owner declarations:
  `IsBeauvilleLaszloGlueingPairAlong`,
  `Module.Flat`,
  `beauvilleLaszloModuleCechSequence`,
  `beauvilleLaszloModuleCechH0Map_surjective`.
* owner abstraction: the ambient owner is the glueing-pair predicate
  `IsBeauvilleLaszloGlueingPairAlong (algebraMap R R') f`; the module property itself is the
  canonical owner predicate `Module.Flat`, not a packaged Beauville-Laszlo flatness wrapper.
* primitive data: the rings `R`, `R'`, the map `algebraMap R R'`, the element `f`, and the
  `R`-module `M`.
* derived API: the two comparison flatness conditions on the canonical base-change module
  `R' ⊗[R] M` and the canonical localization `Away f M`.
*
* Source/core/bridge triage:
  `source-facing`: the Beauville-Laszlo flatness criterion for a single module;
  `core/canonical`: `IsBeauvilleLaszloGlueingPairAlong` and `Module.Flat`;
  `bridge/view`: the base-change module `R' ⊗[R] M` and the localization `Away f M`.
-/

-- Proof sketch: one implication is preserved by base change and localization. For the converse,
-- replace `M` by the glueable module `H⁰(Can(M))` from Remark `15.91.17`, use the Beauville-Laszlo
-- short exact sequence to compare `M` with that replacement, and then prove flatness by the Tor
-- criterion using the exact Čech sequence of the glueing pair.
/-- Lemma 15.91.18: for a Beauville-Laszlo glueing pair `(R → R', f)`, an `R`-module `M` is flat
if and only if its base change is flat over `R'` and its localization `LocalizedModule.Away f M`
is flat over `Localization.Away f`. In mathlib-facing form, the base change of the textbook module
`M ⊗_R R'` is written as `R' ⊗[R] M`. -/
lemma flat_iff_flat_tensor_and_localizedAway_of_beauvilleLaszloGlueingPair
    (f : R) (hpair : IsBeauvilleLaszloGlueingPairAlong (algebraMap R R') f) :
    Module.Flat R M ↔
      Module.Flat R' (R' ⊗[R] M) ∧
        Module.Flat (Localization.Away f) (Away f M) := sorry

end
