import Mathlib
import stacks_project.Chap15.Definition_15_105_3
import stacks_project.Chap15.Definition_15_67_1

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open CategoryTheory
open DerivedCategory.TStructure

universe u

attribute [local instance] HasDerivedCategory.standard

namespace CategoryTheory

section

variable {R : Type u} [CommRing R]

local notation "DMod" => DerivedCategory (ModuleCat R)
local notation "Bounded" => (t.bounded : ObjectProperty DMod)

/- Domain-style sampling for Lemma 15.67.19:
- primary domain: tor-amplitude in the derived category of modules, boundedness via the
  derived-category t-structure, and weak-dimension bounds on the ring;
- sampled owner declarations:
  `HasWeakDimensionLE`,
  `ModuleHasTorDimensionLE`,
  `HasTorAmplitudeIn`,
  `HasFiniteTorDimension`,
  `t.bounded`,
  `DerivedCategory.IsGE`,
  `DerivedCategory.IsLE`;
- best owner abstraction: the ring-side primitive datum for these tor-dimension conclusions is the
  weak-dimension owner `HasWeakDimensionLE R d`, whose module-level consequence is the canonical
  owner `ModuleHasTorDimensionLE`; the stronger Chapter 10 owner `HasGlobalDimensionLE R d`
  belongs only to the bridge layer through the instance from Definition `15.105.3`; the canonical
  way to say that `K` has cohomology concentrated in `[a, b]` is the t-structure owner data
  `K.IsGE a` and `K.IsLE b`, not a parallel pointwise vanishing hypothesis;
- primitive vs. derived:
  primitive data are the ring bound `[HasWeakDimensionLE R d]` and the bounded-support owner
  data `K.IsGE a`, `K.IsLE b`;
  derived API is the resulting tor-amplitude interval and the bounded-derived equivalence;
- source/core/bridge triage:
  `source-facing`: the two tor-dimension consequences below;
  `core/canonical`: `HasWeakDimensionLE`, `ModuleHasTorDimensionLE`, `HasTorAmplitudeIn`,
    `HasFiniteTorDimension`, `t.bounded`, `K.IsGE a`, and `K.IsLE b`;
  `bridge/view`: the instance chain
    `HasGlobalDimensionLE R d ⟹ HasWeakDimensionLE R d ⟹ ModuleHasTorDimensionLE M d`, together
    with the cohomology-vanishing characterization of `K.IsGE a` and `K.IsLE b`; the former stays
    a bridge rather than a primitive hypothesis in this file.
-/

-- Proof sketch: if `K.IsGE a` and `K.IsLE b`, then `H^i(K)` vanishes unless `a ≤ i ≤ b`. For
-- the nonvanishing cohomology objects, the weak-dimension owner gives tor dimension at most `d`,
-- so their degree-zero derived objects have tor-amplitude in
-- `[(-d) - i, -i]`, hence in `[(a - d) - i, b - i]`. Apply Lemma `15.67.9`.
/-- If `R` has weak dimension at most `d` and the cohomology of `K` is concentrated in `[a, b]`,
then `K` has tor-amplitude in `[(a - d), b]`. -/
theorem hasTorAmplitudeIn_of_cohomology_concentrated_of_hasWeakDimensionLE
    (d : ℕ) [HasWeakDimensionLE R d] (K : DMod) (a b : ℤ) (hGE : K.IsGE a) (hLE : K.IsLE b) :
    HasTorAmplitudeIn K (a - (d : ℤ)) b := sorry

-- Proof sketch: if `K` has finite tor dimension, test the defining tor-amplitude condition
-- against the unit module `R[0]` to see that the cohomology of `K` is supported in a finite
-- interval, hence `K` is bounded. Conversely, if `K` is bounded, choose an interval containing its
-- cohomology, apply the previous theorem to obtain finite tor-amplitude, and conclude that `K`
-- has finite tor dimension.
/-- Lemma 15.67.19: over a ring of weak dimension at most `d`, an object of `D(R)` has finite
tor dimension if and only if it satisfies the canonical boundedness owner `t.bounded`, i.e. if
and only if it belongs to the bounded derived category `D^b(R)`. -/
theorem hasFiniteTorDimension_iff_mem_boundedDerivedCategory
    (d : ℕ) [HasWeakDimensionLE R d] (K : DMod) :
    HasFiniteTorDimension K ↔ Bounded K := sorry

end

end CategoryTheory
