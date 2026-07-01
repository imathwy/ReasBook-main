import Mathlib
import stacks_project.Chap15.Definition_15_59_1
import stacks_project.Chap15.Definition_15_67_1

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open CategoryTheory

universe u

attribute [local instance] HasDerivedCategory.standard

namespace CategoryTheory

section

variable {R : Type u} [CommRing R]

local notation "Cpx" => CochainComplex (ModuleCat R) ℤ
local notation "DMod" => DerivedCategory (ModuleCat R)

/- Domain-style sampling:
- primary domain: tor-amplitude in the derived category of modules, expressed through bounded flat
  cochain representatives;
- sampled owner declarations:
  `CategoryTheory.HasTorAmplitudeIn`,
  `CochainComplex.IsTermwiseFlat`,
  `CategoryTheory.HasProjectiveAmplitudeIn`,
  `CategoryTheory.HasInjectiveAmplitudeIn`;
- best owner abstraction: `HasTorAmplitudeIn` is the source-facing/core predicate in this chapter,
  while existence of a bounded flat representative is bridge data describing that owner through a
  concrete model in `CochainComplex (ModuleCat R) ℤ`;
- primitive data: the representative complex `E`, its support conditions `E.IsStrictlyGE a` and
  `E.IsStrictlyLE b`, its termwise flatness `E.IsTermwiseFlat`, and an isomorphism
  `K ≅ DerivedCategory.Q.obj E`;
- derived API: the existential representative criterion for `HasTorAmplitudeIn`. The flat
  representative data should not be promoted to a parallel public owner, since the chapter already
  organizes the domain around tor-amplitude/projective-amplitude/injective-amplitude predicates.

Source/core/bridge triage:
- `source-facing`: tor-amplitude in `[a, b]` for an object of `D(R)`;
- `core/canonical`: `HasTorAmplitudeIn`;
- `bridge/view`: existence of a bounded termwise-flat cochain representative.
-/

-- Proof sketch: for the forward implication, use the tor-amplitude hypothesis together with the
-- bounded-above replacement from Derived Categories, Lemma `13.19.3`, then truncate below `a`
-- and apply Lemma `15.67.2` to identify the new degree-`a` term as flat. For the reverse
-- implication, compute derived tensor products using the flat representative and read off the
-- vanishing of homology outside `[a, b]` from the strict support of the representative complex.
/-- Lemma 15.67.3: an object `K^•` of `D(R)` has tor-amplitude in `[a, b]` if and only if it is
isomorphic in `D(R)` to a cochain complex `E^•` of flat `R`-modules with `E^i = 0` for
`i ∉ [a, b]`. -/
theorem hasTorAmplitudeIn_iff_exists_flat_representative
    (K : DMod) (a b : ℤ) :
    HasTorAmplitudeIn K a b ↔
      ∃ (E : Cpx) (_ : K ≅ DerivedCategory.Q.obj E),
        E.IsStrictlyGE a ∧ E.IsStrictlyLE b ∧ E.IsTermwiseFlat := sorry

end

end CategoryTheory
