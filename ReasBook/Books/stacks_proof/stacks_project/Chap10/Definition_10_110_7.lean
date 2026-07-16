import stacks_proof.stacks_project.Chap10.Definition_10_157_1
import stacks_proof.stacks_project.Chap10.Lemma_10_109_13
import Mathlib.Tactic.StacksAttribute

-- Declarations for this item will be appended below by the statement pipeline.

universe u

variable (R : Type u) [CommRing R]

/-
Source/core/bridge triage:
* source-facing: `IsRegularRing R`, the textbook global regularity condition;
* core/canonical: `IsRegularLocalRing (Localization.AtPrime p.asIdeal)` on each prime
  localization;
* bridge/view: the local-to-global instance sending a regular local ring to a regular ring.

Primitive data are exactly the Noetherian hypothesis and the primewise regular-local owner field.
No extra wrapper data are needed: primewise regularity and Noetherianity are the whole owner, and
all further API should be derived from that owner.
-/
/-- Definition data for Chap10 Definition 10 110 7: a Noetherian ring is regular if every
localization at a prime ideal is a regular local ring. -/
@[stacks 00OD]
class IsRegularRing : Prop extends IsNoetherianRing R where
  isRegularLocalRing_atPrime :
    ∀ p : PrimeSpectrum R, IsRegularLocalRing (Localization.AtPrime p.asIdeal)

variable {R}

/-- A regular ring is Noetherian. -/
instance isNoetherianRing_of_regularRing [h : IsRegularRing R] : IsNoetherianRing R :=
  h.toIsNoetherian

namespace IsRegularRing

/-- A regular ring satisfies Serre's condition `(R_k)` for every `k`. -/
theorem serreConditionR (k : ℕ) [IsRegularRing R] : SerreConditionR R k :=
  { toIsNoetherian := inferInstance
    isRegularLocalRing_localizationAtPrime := fun p _ ↦
      IsRegularRing.isRegularLocalRing_atPrime p }

end IsRegularRing

-- Route correction: this owner file only exposes the class `IsRegularRing` and its direct
-- projections. The regular-local-to-regular bridge now lives in `Lemma_10_110_6`, where the
-- finite-global-dimension localization API is available without reintroducing a transitive proof hole.
