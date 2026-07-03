import stacks_project.Chap10.Definition_10_157_1

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
/-- Definition 10.110.7: a Noetherian ring is regular if every localization at a prime ideal is a
regular local ring. -/
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

-- Proof sketch: regular local rings remain regular after localization at prime ideals, so a
-- regular local ring satisfies the defining primewise condition for `IsRegularRing`.
/-- A regular local ring is regular in the global sense. -/
instance [IsRegularLocalRing R] : IsRegularRing R := sorry
