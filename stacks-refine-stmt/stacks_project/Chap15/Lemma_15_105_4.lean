import Mathlib
import stacks_project.Chap15.Definition_15_105_3
import stacks_project.Chap15.Lemma_15_105_2

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

open CategoryTheory

section

variable (A : Type u) [CommRing A]
variable (B : Type v) [CommRing B] [Algebra A B]
variable (d : ℕ) [HasWeakDimensionLE A d]

/- Domain triage:
- primary domain: weak dimension of commutative rings and its behavior under weakly étale maps;
- sampled owner declarations:
  `HasWeakDimensionLE`,
  `ModuleHasTorDimensionLE`,
  `ModuleCat.hasTorDimensionLE_iff_hasFiniteFlatResolutionLengthLE`,
  `Algebra.IsWeaklyEtale`;
- best owner abstraction: the ring-level owner is `HasWeakDimensionLE`, with the explicit owner
  input `hAB : Algebra.IsWeaklyEtale A B` supplying the flatness input on the structure map and
  tensor-square multiplication;
- primitive vs. derived:
  the primitive data live in the owner classes `HasWeakDimensionLE A d` and
  `Algebra.IsWeaklyEtale A B`;
  the source-facing transfer theorem below and the resulting owner instance on `B` are derived API.

Source/core/bridge triage:
- `source-facing`: `hasWeakDimensionLE_of_isWeaklyEtale`;
- `core/canonical`: `HasWeakDimensionLE` and `Algebra.IsWeaklyEtale`;
- `bridge/view`: the tor-dimension/flat-resolution comparison from Lemma `15.67.6` and the
  owner-level flatness transfer theorem `Module.Flat.of_isWeaklyEtale`.
-/

-- Proof sketch: for `N : ModuleCat B`, restrict scalars to `A`. The owner
-- `HasWeakDimensionLE A d` gives tor dimension at most `d` over `A`, hence by Lemma `15.67.6`
-- a finite flat `A`-resolution of length `d`. Its final syzygy is `A`-flat, so
-- `Module.Flat.of_isWeaklyEtale` upgrades that top term to `B`-flat. Converting the resulting
-- length-`d` flat `B`-resolution back through Lemma `15.67.6` yields tor dimension at most `d`
-- over `B`.
/-- Lemma 15.105.4: if `A → B` is weakly étale and `A` has weak dimension at most `d`, then `B`
has weak dimension at most `d`. -/
theorem hasWeakDimensionLE_of_isWeaklyEtale
    (hAB : Algebra.IsWeaklyEtale A B)
    : HasWeakDimensionLE B d where
  hasTorDimensionLE N := by
    let _ : (algebraMap A B).Flat := hAB.flat
    sorry

-- This transfer is intentionally not registered as a global instance. Unlike base change in
-- Lemma `15.105.7`, the source ring `A` of a weakly étale map `A → B` is not determined by the
-- target owner `HasWeakDimensionLE B d`, so typeclass search would have to guess a noncanonical
-- ambient algebra `A → B`.

end
