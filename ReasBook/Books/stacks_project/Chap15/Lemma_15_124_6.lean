import Mathlib
import stacks_project.Chap10.Lemma_10_155_1
import stacks_project.Chap10.Lemma_10_155_2
import stacks_project.Chap15.Definition_15_124_1

-- Declarations for this item will be appended below by the statement pipeline.

universe u

open IsExtensionOfValuationRings

section

variable {A : Type u} [CommRing A] [IsDomain A] [ValuationRing A]
variable {Ah : Type u} [CommRing Ah] [Algebra A Ah] [IsHenselizationOf A Ah]

/- Domain-style sampling for Lemma 15.124.6:
- primary domain: valuation rings and weakly unramified extensions along henselization towers;
- sampled owner declarations:
  `IsExtensionOfValuationRings`,
  `WeaklyUnramified`,
  `localizationAtPrime_isWeaklyUnramifiedExtensionOfValuationRings_of_etale`,
  `IsHenselizationOf` / `IsStrictHenselizationOf`;
- best owner abstraction: the primitive source data are the henselization and
  strict-henselization owners on the two structural maps, while the valuation-ring structures,
  extension-of-valuation-rings instances, and weakly-unramified predicates are derived API;
- primitive-vs-derived split:
  primitive data: the chosen henselization `A → Ah` and strict henselization `Ah → Ash`;
  derived API: `IsDomain`, `ValuationRing`, `IsExtensionOfValuationRings`, and the two
  `WeaklyUnramified` statements.

Source/core/bridge triage:
- `source-facing`: the tower statement that both comparison maps in the henselization tower are
  weakly unramified;
- `core/canonical`: `IsExtensionOfValuationRings` and `WeaklyUnramified`;
- `bridge/view`: the étale filtered-colimit presentations supplied by
  `IsHenselizationOf` and `IsStrictHenselizationOf`, together with Lemma `15.124.5` on each étale
  local stage.
-/

/-- A henselization of a valuation ring is again a domain. -/
instance : IsDomain Ah := sorry

/-- A henselization of a valuation ring is again a valuation ring. -/
instance : ValuationRing Ah := sorry

/-- The canonical map from a valuation ring to its henselization is an extension of valuation
rings. -/
instance : IsExtensionOfValuationRings A Ah := sorry

/-- A henselization of a valuation ring is weakly unramified over the base valuation ring. -/
theorem henselization_weaklyUnramified : WeaklyUnramified A Ah := sorry

section

variable {Ash : Type u} [CommRing Ash] [Algebra Ah Ash] [IsStrictHenselizationOf Ah Ash]

/-- A strict henselization over a henselization of a valuation ring is again a domain. -/
instance : IsDomain Ash := sorry

/-- A strict henselization over a henselization of a valuation ring is again a valuation ring. -/
instance : ValuationRing Ash := sorry

/-- The canonical map from a henselization of a valuation ring to a strict henselization over it
is an extension of valuation rings. -/
instance :
    IsExtensionOfValuationRings Ah Ash := sorry

/-- A strict henselization over a henselization of a valuation ring is weakly unramified. -/
theorem strictHenselizationOverHenselization_weaklyUnramified :
    WeaklyUnramified Ah Ash := sorry

end

variable {Ash : Type u} [CommRing Ash] [Algebra Ah Ash]

-- Proof sketch: combine the two canonical weakly unramified statements for the maps
-- `A → Ah` and `Ah → Ash`. The preceding instances record that both target rings remain valuation
-- rings and that both algebra maps are extensions of valuation rings.
/-- Lemma 15.124.6: if `A` is a valuation ring, `Ah` is a henselization of `A`, and `Ash` is a
strict henselization of `Ah`, then the inclusions `A ⊆ Ah` and `Ah ⊆ Ash` are extensions of
valuation rings and both are weakly unramified. -/
theorem henselization_tower_weaklyUnramified [IsStrictHenselizationOf Ah Ash] :
    WeaklyUnramified A Ah ∧ WeaklyUnramified Ah Ash := by
  exact ⟨henselization_weaklyUnramified, strictHenselizationOverHenselization_weaklyUnramified⟩

end
