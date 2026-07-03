import Mathlib
import StacksProject_2024.Chap15.Lemma_15_60_1
import StacksProject_2024.Chap15.Lemma_15_75_2

noncomputable section

open CategoryTheory
open scoped DerivedTensorWithAlgebra

universe u

attribute [local instance] HasDerivedCategory.standard

namespace CategoryTheory

section

variable {R : Type u} [CommRing R]
variable {ι : Type*} [Finite ι]

local notation "DMod" => DerivedCategory (ModuleCat R)

/- Domain-style sampling for Lemma 15.75.12:
- primary domain: local-global perfection in `D(R)` under localization away from a finite
  principal-open cover;
- sampled owner declarations:
  `DerivedCategory.IsPerfect`,
  `isPseudoCoherent_of_localizationAway_unitIdeal`,
  `hasTorAmplitudeIn_of_localizationAway_unitIdeal`,
  `isPerfect_iff_isPseudoCoherent_and_hasFiniteTorDimension`;
- best owner abstraction: this item is `source-facing`, while the canonical owners are
  `DerivedCategory.IsPerfect` with object-prefix theorem surface `K.IsPerfect`,
  `K.IsPseudoCoherent`, and `HasFiniteTorDimension K`;
- primitive vs. derived:
  the primitive data are the finite family `f`, the unit-ideal hypothesis, and the localized
  perfectness assumptions;
  pseudo-coherence and finite tor dimension are derived owner-level consequences and should not be
  stored as parallel local data;
- source/core/bridge triage:
  `source-facing`: perfection descends from a finite localization-away cover;
  `core/canonical`: the perfectness characterization by pseudo-coherence and finite tor dimension;
  `bridge/view`: the localized derived base-change objects
    `K ⊗[R]^L[Localization.Away (f i)]`. -/

-- Proof sketch: use Lemma `15.75.2` to reduce perfection to pseudo-coherence and finite tor
-- dimension. Pseudo-coherence descends directly by Lemma `15.65.14 (2)`. For finite tor
-- dimension, choose a tor-amplitude interval on each localization, enlarge them to one common
-- interval over the finite index set, descend that uniform tor-amplitude by Lemma `15.67.16`, and
-- then reassemble perfection with Lemma `15.75.2`.
/-- Lemma 15.75.12: if a finite family `f : ι → R` generates the unit ideal and each derived
localization `K^• ⊗_R R_{f_i}` is perfect, then `K^•` is perfect. -/
theorem isPerfect_of_localizationAway_unitIdeal
    (f : ι → R) (hunit : Ideal.span (Set.range f) = ⊤) (K : DMod)
    (hloc : ∀ i, (K ⊗[R]^L[Localization.Away (f i)]).IsPerfect) :
    K.IsPerfect := sorry

end

end CategoryTheory
