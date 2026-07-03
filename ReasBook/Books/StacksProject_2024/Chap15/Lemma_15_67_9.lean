import StacksProject_2024.Chap13.Definition_13_11_3
import StacksProject_2024.Chap13.Lemma_13_27_9
import StacksProject_2024.Chap15.Definition_15_67_1

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open DerivedCategory
open scoped CategoryTheory

universe u

attribute [local instance] HasDerivedCategory.standard

namespace CategoryTheory

section

variable {R : Type u} [CommRing R]

local notation "Mod" => ModuleCat R
local notation "DbMod" => Dᵇ(Mod)
local notation "Hb" => boundedDerivedHomologyFunctor Mod

/- Domain-style sampling for Lemma 15.67.9:
- primary domain: tor-amplitude and finite tor dimension in the bounded derived category `D^b(R)`,
  read through the canonical bounded-derived cohomology functors;
- sampled owner declarations:
  `HasTorAmplitudeIn`,
  `HasFiniteTorDimension`,
  `ModuleHasFiniteTorDimension`,
  `Dᵇ(ModuleCat R)`,
  `boundedDerivedHomologyFunctor`,
  `shiftedCohomology`,
  `hasTorAmplitudeIn_shift_iff`;
- best owner abstraction: the tor-amplitude owner is `HasTorAmplitudeIn K a b`, boundedness is
  carried canonically by `K : DbMod`; the cohomology modules of such a bounded object should
  be read through the chapter owner `Hb i : Dᵇ(ModuleCat R) ⥤ ModuleCat R`, and finite tor
  dimension for those modules should use the module-level owner
  `ModuleHasFiniteTorDimension` instead of re-expanding it through the degree-zero embedding; the
  intrinsic shifted cohomology object attached to `H^i(K)` should be read through the chapter owner
  `shiftedCohomology Mod K.obj i` rather than through a local
  `M[0][i]` spelling; the only bridge-level input needed on the public surface is the companion
  shift theorem `hasTorAmplitudeIn_shift_iff`, which lets the hypotheses be read on the intrinsic
  shifted cohomology objects
  `shiftedCohomology Mod K.obj i`, rather than as raw `singleFunctor` packaging or as a second
  coordinate-level interval API;
- primitive vs. derived:
  primitive data are the bounded derived object `K` and the termwise tor-amplitude hypotheses on
  its intrinsic shifted bounded-derived cohomology objects `shiftedCohomology Mod K.obj i`;
  derived API is the finite-tor-dimension consequence, obtained by packaging interval existence;
- source/core/bridge triage:
  `source-facing`: the two textbook bounded-derived theorems below;
  `core/canonical`: `HasTorAmplitudeIn`, `HasFiniteTorDimension`,
  `ModuleHasFiniteTorDimension`, `Dᵇ(ModuleCat R)`, `Hb`, and `shiftedCohomology`;
  `bridge/view`: the boundedness owner on `K`, the degree-zero embedding `M ↦ M[0]`, and the
    shift-transport bridge `hasTorAmplitudeIn_shift_iff`.

This file therefore keeps the source-facing bounded-derived statements, while reusing the chapter
owners `boundedDerivedHomologyFunctor`, `shiftedCohomology`,
`ModuleHasFiniteTorDimension`, and the Chapter 13 bounded-object/cohomology bridge instead of
spelling a parallel representative API here.
-/

/-- Lemma 15.67.9: if `K` is a bounded derived object of `R`-modules and each cohomology module
`H^i(K)`, placed in cohomological degree `i`, has tor-amplitude in `[a, b]`, then `K` has
tor-amplitude in `[a, b]`. The canonical owner for that shifted cohomology object is
`shiftedCohomology Mod K.obj i`. -/
theorem hasTorAmplitudeIn_of_bounded_of_homology_hasTorAmplitudeIn
    (a b : ℤ) (K : DbMod)
    (hH : ∀ i : ℤ, HasTorAmplitudeIn (shiftedCohomology Mod K.obj i) a b) :
    HasTorAmplitudeIn K.obj a b := sorry

-- Proof sketch: boundedness leaves only finitely many possibly nonzero cohomology modules, so the
-- finite tor-dimension intervals for the degree-zero cohomology modules admit common endpoints;
-- transport those intervals to the intrinsic shifted cohomology objects
-- `shiftedCohomology Mod K.obj i` by `hasTorAmplitudeIn_shift_iff`, then apply the first theorem.
/-- If every cohomology module of a bounded derived object has finite tor dimension, then the
bounded derived object itself has finite tor dimension. -/
theorem hasFiniteTorDimension_of_bounded_of_homology_hasFiniteTorDimension
    (K : DbMod)
    (hH : ∀ i : ℤ, ModuleHasFiniteTorDimension ((Hb i).obj K)) :
    HasFiniteTorDimension K.obj := sorry

end

end CategoryTheory
