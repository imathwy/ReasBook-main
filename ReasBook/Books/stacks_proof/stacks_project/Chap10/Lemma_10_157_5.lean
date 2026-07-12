import Mathlib
import StacksProject_2024.Chap10.Definition_10_37_11
import StacksProject_2024.Chap10.Definition_10_110_7
import StacksProject_2024.Chap10.Lemma_10_106_3
import StacksProject_2024.Chap10.Lemma_10_157_4_Serre_s_criterion_for_normality

-- Declarations for this item will be appended below by the statement pipeline.

universe u

section

variable {R : Type u} [CommRing R]

/-
Domain-style sampling:
* primary domain: regular and normal Noetherian commutative rings;
* sampled owner declarations:
  `IsRegularRing`,
  `IsNormalRing`,
  `IsRegularRing.isRegularLocalRing_atPrime`,
  `IsNormalRing.isNormalLocalizationAtPrime`;
* best owner abstraction: the source-facing hypothesis is the chapter owner `IsRegularRing R`, and
  the conclusion should be the chapter owner `IsNormalRing R`;
* primitive data vs derived API: the primitive public input is only `[IsRegularRing R]`; the old
  primewise pair of `IsDomain` and `IsIntegrallyClosed` instances is derived local API already
  packaged by `IsNormalRing`.

Layering:
* `source-facing`: the textbook statement that a regular ring is normal;
* `core/canonical`: the owner predicates `IsRegularRing R` and `IsNormalRing R`;
* `bridge/view`: the prime-local domain and integrally-closed consequences recovered from
  `IsNormalRing.isNormalLocalizationAtPrime`.
-/

-- Proof sketch: a regular ring satisfies the primewise regular-local hypothesis built into
-- `IsRegularRing`; Serre's criterion from Lemma `10.157.4` then yields that the ring is normal.
/-- Lemma 10.157.5: a regular ring is normal. -/
@[stacks 0567]
theorem isNormalRing_of_isRegularRing [IsRegularRing R] : IsNormalRing R := by
  -- Proof comment: regularity gives the codimension-one half `(R₁)` directly.
  have hR : SerreConditionR R 1 := IsRegularRing.serreConditionR (R := R) 1
  have hCM : CohenMacaulayRing R := by
    -- Proof comment: regularity localizes to a regular local ring at every prime, and regular
    -- local rings are Cohen--Macaulay as self-modules.
    refine { toIsNoetherian := inferInstance, toLocallyCohenMacaulay := ?_ }
    refine { toFinite := inferInstance, localizedModule_cohenMacaulay := ?_ }
    intro p
    let _ : IsRegularLocalRing (Localization.AtPrime p.asIdeal) :=
      IsRegularRing.isRegularLocalRing_atPrime p
    simpa using
      (regularLocalRing_selfModule_cohenMacaulay
        (R := Localization.AtPrime p.asIdeal))
  let _ : CohenMacaulayRing R := hCM
  -- Proof comment: the regular-to-Cohen--Macaulay bridge upgrades regularity to `(S₂)`.
  have hS : SerreConditionS R 2 := CohenMacaulayRing.serreConditionS (R := R) 2
  -- Proof comment: Serre's criterion closes once both owner-level Serre conditions are available.
  exact isNormalRing_iff_serreConditionR_one_and_serreConditionS_two (R := R) |>.2 ⟨hR, hS⟩

end
