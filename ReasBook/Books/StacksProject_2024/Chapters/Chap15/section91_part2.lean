import Mathlib
import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
import Mathlib.Algebra.Module.Torsion.PrimaryComponent
import Mathlib.CategoryTheory.Monoidal.Tor
import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory
import Mathlib.RingTheory.AdicCompletion.Algebra
import Mathlib.RingTheory.Localization.Away.Basic

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Lemma_15_91_18 (from Chap15) -/
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

/-! ### Lemma_15_91_19 (from Chap15) -/
open scoped TensorProduct

noncomputable section

universe u w

section

variable {R : Type u} [CommRing R]
variable {R' : Type u} [CommRing R'] [Algebra R R']
variable {M : Type w} [AddCommMonoid M] [Module R M]
local notation "Away" => LocalizedModule.Away

/- Domain-style sampling:
* primary domain: Beauville-Laszlo descent for finite projective modules over commutative rings.
* sampled owner declarations:
  `IsBeauvilleLaszloGlueingPairAlong`,
  `Module.FiniteProjective`,
  `flat_iff_flat_tensor_and_localizedAway_of_beauvilleLaszloGlueingPair`,
  `moduleFinite_iff_finite_tensor_and_localizedAway_of_quotientMapBijective`.
* owner abstraction: the source-facing Beauville-Laszlo descent statement should use the chapter
  owner predicate `Module.FiniteProjective`, while the glueing hypothesis is still owned by
  `IsBeauvilleLaszloGlueingPairAlong (algebraMap R R') f`.
* primitive data: the rings `R`, `R'`, the algebra map `R → R'`, the element `f`, and the
  module `M`.
* derived API: the finite-projective comparisons for the canonical base change `R' ⊗[R] M` and
  localization `Away f M`.
*
* Source/core/bridge triage:
  `source-facing`: the Beauville-Laszlo finite-projective criterion below;
  `core/canonical`: `IsBeauvilleLaszloGlueingPairAlong` and `Module.FiniteProjective`;
  `bridge/view`: the canonical base-change module `R' ⊗[R] M` and localization `Away f M`.
-/

-- Proof sketch: for the forward implication, finite projective modules remain finite projective
-- after scalar extension to `R'` and localization away from `f`. For the converse, use Lemma
-- `15.91.18` to descend flatness from `R' ⊗[R] M` and `M_f`, use Lemma `15.91.4` to descend
-- finite generation, and then package the result in the canonical owner predicate
-- `Module.FiniteProjective`.
/-- Lemma 15.91.19: for a Beauville-Laszlo glueing pair `(R → R', f)`, an `R`-module `M` is
finite projective if and only if its base change `R' ⊗[R] M` is finite and projective over `R'`
and its localization `LocalizedModule.Away f M` is finite and projective over
`Localization.Away f`. -/
lemma finiteProjective_iff_tensor_and_localizedAway_finiteProjective_of_beauvilleLaszloGlueingPair
    (f : R) (hpair : IsBeauvilleLaszloGlueingPairAlong (algebraMap R R') f) :
    Module.FiniteProjective R M ↔
      Module.FiniteProjective R' (R' ⊗[R] M) ∧
        Module.FiniteProjective (Localization.Away f) (Away f M) := by
  sorry

end

/-! ### Remark_15_91_20 (from Chap15) -/
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
