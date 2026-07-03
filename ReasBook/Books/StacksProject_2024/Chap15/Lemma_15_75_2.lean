import Mathlib
import StacksProject_2024.Chap10.Lemma_10_55_6
import StacksProject_2024.Chap10.Lemma_10_78_2
import StacksProject_2024.Chap13.Lemma_13_15_4
import StacksProject_2024.Chap15.Definition_15_65_1
import StacksProject_2024.Chap15.Definition_15_67_1
import StacksProject_2024.Chap15.Definition_15_75_1

noncomputable section

open CategoryTheory

universe u

attribute [local instance] HasDerivedCategory.standard

namespace CategoryTheory

section

variable {R : Type u} [CommRing R]

local notation "ModR" => ModuleCat R
local notation "Cpx" => CochainComplex ModR ℤ
local notation "DMod" => DerivedCategory ModR

/- Domain-style sampling for Lemma 15.75.2:
- primary domain: perfect objects in `D(R)` and their concrete finite-projective representatives;
- sampled owner declarations:
  `DerivedCategory.IsPerfect`,
  `DerivedCategory.IsPseudoCoherent`,
  `HasTorAmplitudeIn`,
  `finiteProjectiveModuleProperty`,
  `CochainComplex.MinusWithTermsIn`;
- best owner abstraction: the main perfectness predicate is the source-facing owner
  `K.IsPerfect`, while explicit representative data should reuse the existing bounded-above owner
  `CochainComplex.MinusWithTermsIn (finiteProjectiveModuleProperty R)` rather than re-bundling
  boundedness through `CochainComplex.IsBoundedFiniteProjective` when the theorem already
  specifies the exact support interval `[a, b]`;
- primitive vs. derived:
  primitive data are the derived object `K`, the tor-amplitude interval `[a, b]`, and a
  representative complex with termwise finite-projective terms and explicit support bounds;
  the global boundedness package `CochainComplex.IsBoundedFiniteProjective` is derived from those
  explicit bounds and should not be duplicated in the representative theorem below;
- source/core/bridge triage:
  `source-facing`: perfectness characterized by pseudo-coherence and finite tor dimension;
  `core/canonical`: `K.IsPerfect`, `K.IsPseudoCoherent`, `HasFiniteTorDimension K`, and the owner
    `CochainComplex.MinusWithTermsIn (finiteProjectiveModuleProperty R)`;
  `bridge/view`: the representative theorem below, which presents perfectness data through a
    chosen bounded-above finite-projective model with fixed support bounds.
-/

-- Proof sketch: combine the bounded finite-projective representative from `IsPerfect` with
-- Lemma `15.65.5` and Lemma `15.67.3` to obtain pseudo-coherence and finite tor dimension, and
-- conversely use a bounded flat representative in the given tor-amplitude range together with
-- Lemma `15.67.2` and Algebra, Lemma `10.78.2` to replace the leftmost flat term by a finite
-- projective module.
/-- Lemma 15.75.2: an object `K^•` of `D(R)` is perfect if and only if it is pseudo-coherent and
has finite tor dimension. -/
theorem isPerfect_iff_isPseudoCoherent_and_hasFiniteTorDimension
    (K : DMod) :
    K.IsPerfect ↔ K.IsPseudoCoherent ∧ HasFiniteTorDimension K := sorry

-- Proof sketch: choose a bounded-above finite-free representative from pseudo-coherence, truncate
-- it below `a` using the tor-amplitude hypothesis, apply Lemma `15.67.2` to show the new degree
-- `a` term is flat, and then invoke Algebra, Lemma `10.78.2` to upgrade that finite flat module
-- to a finite projective one. The bounded-above finite-projective data are then recorded through
-- the canonical owner `CochainComplex.MinusWithTermsIn (finiteProjectiveModuleProperty R)`, while
-- the explicit lower and upper support bounds remain separate source-facing data.
/-- For a pseudo-coherent object, tor-amplitude in `[a, b]` yields a
representative by finite projective `R`-modules concentrated in degrees `[a, b]`. -/
theorem exists_strictlySupported_finiteProjective_complex_of_isPseudoCoherent_of_hasTorAmplitudeIn
    {K : DMod} {a b : ℤ}
    (hKpc : K.IsPseudoCoherent) (hamp : HasTorAmplitudeIn K a b) :
    ∃ E : CochainComplex.MinusWithTermsIn (finiteProjectiveModuleProperty R),
      ∃ (_ : K ≅ DerivedCategory.Q.obj (E : Cpx)),
        (E : Cpx).IsStrictlyGE a ∧ (E : Cpx).IsStrictlyLE b := sorry

end

end CategoryTheory
