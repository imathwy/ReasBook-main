import Mathlib
import StacksProject_2024.Chap13.Lemma_13_11_6
import StacksProject_2024.Chap15.Definition_15_75_1

noncomputable section

open CategoryTheory

universe u

attribute [local instance] HasDerivedCategory.standard

namespace CategoryTheory

section

variable {R : Type u} [CommRing R]

local notation "DbMod" => boundedDerivedCategory (ModuleCat R)
local notation "Hb" => boundedDerivedHomologyFunctor (ModuleCat R)

/- Domain-style sampling for Lemma 15.75.7:
- primary domain: perfect objects in the bounded derived category `D^b(R)`, with the cohomology
  modules viewed through the chapter owners `DerivedCategory.IsPerfect` and `ModuleCat.IsPerfect`;
- sampled owner declarations:
  `boundedDerivedCategory`,
  `boundedDerivedHomologyFunctor`,
  `DerivedCategory.IsPerfect`,
  `ModuleCat.IsPerfect`,
  `boundedAbove_isPseudoCoherent_of_homology`,
  `hasFiniteTorDimension_of_bounded_of_homology_hasFiniteTorDimension`,
  `isPerfect_iff_isPseudoCoherent_and_hasFiniteTorDimension`;
- best owner abstraction: this item is `source-facing`, while the `core/canonical` owners are the
  bounded derived category `DbMod`, the perfectness owner `K.obj.IsPerfect`, and the owner-level
  reductions to pseudo-coherence and finite tor dimension;
- primitive vs. derived:
  primitive data are the bounded derived object `K` and the degreewise hypotheses that each
  bounded-derived cohomology module `((Hb i).obj K)` is perfect;
  derived API is the conclusion that the bounded derived object itself is perfect, obtained by
  reusing the chapter owners for pseudo-coherence and tor dimension rather than introducing a
  parallel local wrapper;
- source/core/bridge triage:
  `source-facing`: the theorem below about bounded derived complexes with perfect cohomology;
  `core/canonical`: `DbMod`, `DerivedCategory.IsPerfect`, `K.IsPseudoCoherent`, and
    `HasFiniteTorDimension K`;
  `bridge/view`: the bounded-derived cohomology functors `Hb i` landing in modules, where
    perfectness is read by the module-level owner `ModuleCat.IsPerfect`.

This file should therefore keep the source-facing bounded-derived theorem, while phrasing its
surface directly with the chapter owners instead of a parallel local API.
-/

-- Proof sketch: apply `boundedAbove_isPseudoCoherent_of_homology` to the bounded object `K.obj`
-- and the perfect cohomology hypotheses to obtain pseudo-coherence, use
-- `hasFiniteTorDimension_of_bounded_of_homology_hasFiniteTorDimension` degreewise to obtain
-- finite tor dimension, and conclude by
-- `isPerfect_iff_isPseudoCoherent_and_hasFiniteTorDimension`.
/-- Lemma 15.75.7: if a bounded derived `R`-complex has perfect cohomology modules in every
degree, then the complex itself is perfect. -/
theorem isPerfect_of_bounded_of_homology_isPerfect
    (K : DbMod)
    (hH : ∀ i : ℤ, ((Hb i).obj K).IsPerfect) :
    K.obj.IsPerfect := sorry

end

end CategoryTheory
