import Mathlib.Data.List.TFAE
import stacks_project.Chap15.Definition_15_105_1
import stacks_project.Chap15.Definition_15_105_3

-- Declarations for this item will be appended below by the statement pipeline.

universe u

section

variable (A : Type u) [CommRing A]

/- Domain-style sampling:
- primary domain: commutative algebra of weak dimension, absolute flatness, zero-dimensional
  reduced rings, and prime localizations;
- sampled owner declarations:
  `HasWeakDimensionLE`,
  `ModuleCat.hasTorDimensionLE_zero_iff_flat`,
  `IsAbsolutelyFlatRing`,
  `Ring.KrullDimLE.of_isLocalization`,
  `Ring.KrullDimLE.isField_of_isReduced`;
- best owner abstraction: the source-facing clause `(1)` should use the chapter owner
  `HasWeakDimensionLE A 0`, with the module-level zero-step bridge supplied canonically by
  `ModuleCat.hasTorDimensionLE_zero_iff_flat`; clause `(2)` should use the project owner
  `IsAbsolutelyFlatRing`, and clauses `(3)` and `(4)` should use the canonical mathlib owners
  `Ring.KrullDimLE 0` and `Localization.AtPrime`;
- primitive vs. derived:
  primitive data is just the ring `A` together with these owner predicates on `A` and its prime
  localizations;
  the only source-facing declaration needed here is the four-way `TFAE`, so no extra wrapper
  theorem is warranted.

Source/core/bridge triage:
- `source-facing`: the four-way equivalence matching the Stacks clause list;
- `core/canonical`: `HasWeakDimensionLE`, `IsAbsolutelyFlatRing`, `Ring.KrullDimLE 0`, and
  `Localization.AtPrime`;
- `bridge/view`: the `TFAE` theorem itself, which compares the source clauses directly without
  introducing any extra packaged interface.
-/

-- Proof sketch: `(1) ↔ (2)` follows by unpacking weak dimension `≤ 0` and using that tor
-- dimension `≤ 0` is flatness for every module. For `(2) → (3)`, absolute flatness makes every
-- finitely generated ideal pure, hence idempotent-generated, so basic opens are clopen; this
-- forces every prime ideal to be maximal, and nilpotents vanish. For `(3) → (4)`, transport
-- `Ring.KrullDimLE 0 A` to each `Localization.AtPrime p.asIdeal` via
-- `Ring.KrullDimLE.of_isLocalization`, then combine with reducedness and
-- `Ring.KrullDimLE.isField_of_isReduced`. For `(4) → (2)`, flatness is local at prime
-- localizations, and modules over fields are flat.
/-- Lemma 15.105.5: for a commutative ring `A`, the following are equivalent: `A` has weak
dimension at most `0`; `A` is absolutely flat; `A` is reduced and every prime ideal is maximal,
formalized as `IsReduced A ∧ Ring.KrullDimLE 0 A`; and every canonical prime localization
`Localization.AtPrime p.asIdeal` is a field. -/
theorem weakDimensionLEZero_tfae :
    List.TFAE
      [ HasWeakDimensionLE A 0
      , IsAbsolutelyFlatRing A
      , IsReduced A ∧ Ring.KrullDimLE 0 A
      , ∀ p : PrimeSpectrum A, IsField (Localization.AtPrime p.asIdeal)
      ] := sorry

/-- An absolutely flat commutative ring has weak dimension at most `0`. -/
theorem hasWeakDimensionLEZero_of_isAbsolutelyFlatRing [IsAbsolutelyFlatRing A] :
    HasWeakDimensionLE A 0 := by
  have h : IsAbsolutelyFlatRing A ↔ HasWeakDimensionLE A 0 :=
    (weakDimensionLEZero_tfae A).out 1 0
  exact h.mp inferInstance

/-- A commutative ring of weak dimension at most `0` is absolutely flat. -/
theorem isAbsolutelyFlatRing_of_hasWeakDimensionLEZero [HasWeakDimensionLE A 0] :
    IsAbsolutelyFlatRing A := by
  have h : HasWeakDimensionLE A 0 ↔ IsAbsolutelyFlatRing A :=
    (weakDimensionLEZero_tfae A).out 0 1
  exact h.mp inferInstance

/-- An absolutely flat commutative ring is reduced. -/
theorem isReduced_of_isAbsolutelyFlatRing [IsAbsolutelyFlatRing A] :
    IsReduced A := by
  have h : IsAbsolutelyFlatRing A ↔ IsReduced A ∧ Ring.KrullDimLE 0 A :=
    (weakDimensionLEZero_tfae A).out 1 2
  exact (h.mp inferInstance).1

end
