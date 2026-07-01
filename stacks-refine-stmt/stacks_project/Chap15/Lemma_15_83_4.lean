import Mathlib
import stacks_project.Chap15.Definition_15_83_1

-- Declarations for this item will be appended below by the statement pipeline.

universe u

open CategoryTheory

namespace Algebra

/- Domain-style sampling for Lemma 15.83.4:
- primary domain: perfect ring maps for flat finitely presented algebras;
- sampled owner declarations:
  `RingHom.IsPerfectRingMap`,
  `RingHom.IsPseudoCoherentRingMap`,
  `CategoryTheory.ModuleHasFiniteTorDimension`,
  `ModuleCat.hasTorDimensionLE_zero_iff_flat`;
- best owner abstraction: the source-facing conclusion belongs on the ring-map owner
  `(algebraMap A B).IsPerfectRingMap`; pseudo-coherence and finite Tor dimension should be derived
  from the canonical chapter owners rather than by a local wrapper;
- primitive vs. derived:
  primitive public data are the flatness and finite-presentation instances on `A → B`;
  derived API is the perfectness instance, whose fields come from the chapter owner
  `RingHom.IsPseudoCoherentRingMap` and the zero-step Tor-dimension bridge
  `ModuleCat.hasTorDimensionLE_zero_iff_flat`.

Source/core/bridge triage:
- `source-facing`: the instance below;
- `core/canonical`: `RingHom.IsPerfectRingMap`, `RingHom.IsPseudoCoherentRingMap`,
  `ModuleHasFiniteTorDimension`;
- `bridge/view`: the zero-step equivalence between module flatness and tor dimension at most `0`.
-/
/- Proof sketch: the pseudo-coherence field is the substantive part of the source argument,
obtained by descending the flat finitely presented map to a flat finite type model over a finite
type `ℤ`-algebra and applying the pseudo-coherence ascent/descent results from `15.82`. The finite
Tor-dimension field is the flat-implies-tor-dimension-`0` clause for the canonical module
`ModuleCat.of A B`. -/
/-- Lemma 15.83.4: a ring map `A → B` which is flat and of finite presentation is perfect. -/
instance isPerfectRingMap_of_flat_of_finitePresentation
    (A : Type u) (B : Type u) [CommRing A] [CommRing B] [Algebra A B]
    [Module.Flat A B] [Algebra.FinitePresentation A B] : (algebraMap A B).IsPerfectRingMap where
  toIsPseudoCoherentRingMap := by
    sorry
  hasFiniteTorDimension := by
    sorry

end Algebra
