import Mathlib
import StacksProject_2024.Chap10.Lemma_10_78_6
import StacksProject_2024.Chap15.Lemma_15_91_6
import StacksProject_2024.Chap15.Lemma_15_91_18

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
