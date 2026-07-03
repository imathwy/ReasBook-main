import Mathlib
import StacksProject_2024.Chap15.Lemma_15_91_19
import StacksProject_2024.Chap15.Theorem_15_91_16

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open scoped TensorProduct

noncomputable section

universe u v

/-
Domain-style sampling for Remark 15.91.20:
- primary domain: Beauville-Laszlo descent for modules over the completion pair
  `R → principalAdicCompletion f`;
- sampled owner declarations:
  `beauvilleLaszloGlueableCan_isEquivalence`,
  `finiteProjective_iff_tensor_and_localizedAway_finiteProjective_of_beauvilleLaszloGlueingPair`,
  `IsBeauvilleLaszloGlueingPairAlong`,
  `principalAdicCompletion`;
- best owner abstraction: the chapter owners for the Beauville-Laszlo equivalence and finite-
  projective descent; the completion pair is only a specialization parameter, not a second owner;
- primitive data: `R`, `f`, the completion algebra map `R → principalAdicCompletion f`, and in
  the finite-projective clause the module `M`;
- derived API: the completion specializations obtained by instantiating the two owner theorems at
  `R' = principalAdicCompletion f`.

Source/core/bridge triage:
- `source-facing`: the remark that the Beauville-Laszlo criteria remain valid for the completion
  pair;
- `core/canonical`: `beauvilleLaszloGlueableCan_isEquivalence`,
  `finiteProjective_iff_tensor_and_localizedAway_finiteProjective_of_beauvilleLaszloGlueingPair`,
  and `IsBeauvilleLaszloGlueingPairAlong`;
- `bridge/view`: the completion specialization recorded below.

Since this file is only a bridge/view specialization and the upstream owners already expose the
exact interfaces needed here, the refined file keeps direct specialized recalls instead of
parallel local theorem names.
-/

section

variable {R : Type u} [CommRing R]
variable (f : R)
variable (hpair : IsBeauvilleLaszloGlueingPairAlong
  (algebraMap R (principalAdicCompletion f)) f)

/- Remark 15.91.20: specializing Theorem 15.91.16 to the completion pair
`R → principalAdicCompletion f` yields the Beauville-Laszlo equivalence for all glueable
`R`-modules, with no nonzerodivisor hypothesis on `f`. -/
#check (beauvilleLaszloGlueableCan_isEquivalence f hpair :
  Functor.IsEquivalence
    ((beauvilleLaszloGlueableProperty (principalAdicCompletion f) f).ι ⋙
      formalGlueingSingleFunctor (principalAdicCompletion f) f))

section

variable {M : Type v} [AddCommGroup M] [Module R M]

/- The same completion specialization of Lemma 15.91.19 characterizes finite projectivity from
the completion and localization data, without any glueability assumption on `M` and allowing
nonzero `f`-power torsion. -/
#check (finiteProjective_iff_tensor_and_localizedAway_finiteProjective_of_beauvilleLaszloGlueingPair
  f hpair :
  Module.FiniteProjective R M ↔
    Module.FiniteProjective (principalAdicCompletion f) (principalAdicCompletion f ⊗[R] M) ∧
      Module.FiniteProjective (Localization.Away f) (LocalizedModule.Away f M))

end

end
