import Mathlib
import StacksProject_2024.Chap10.Lemma_10_155_1
import StacksProject_2024.Chap10.Lemma_10_155_2
import StacksProject_2024.Chap15.Definition_15_124_1
import StacksProject_2024.Chap15.Lemma_15_45_6

-- Declarations for this item will be appended below by the statement pipeline.

universe u

open IsExtensionOfValuationRings
open IsLocalRing

attribute [local instance] FractionRing.liftAlgebra FractionRing.isScalarTower_liftAlgebra

section

/-- Helper for Lemma 15.124.6: in a tower of valuative extensions of fraction fields, the induced
maps on value groups compose as expected. -/
private theorem mapValueGroupWithZero_comp_of_tower
    {K : Type*} {L : Type*} {M : Type*}
    [Field K] [Field L] [Field M]
    [ValuativeRel K] [ValuativeRel L] [ValuativeRel M]
    [Algebra K L] [Algebra L M] [Algebra K M] [IsScalarTower K L M]
    [ValuativeExtension K L] [ValuativeExtension L M] [ValuativeExtension K M] :
    (ValuativeExtension.mapValueGroupWithZero L M).comp
        (ValuativeExtension.mapValueGroupWithZero K L) =
      ValuativeExtension.mapValueGroupWithZero K M := by
  ext γ
  -- It is enough to compare both maps on actual valuations of field elements.
  obtain ⟨x, rfl⟩ := ValuativeRel.valuation_surjective (K := K) γ
  simp [ValuativeExtension.mapValueGroupWithZero_valuation, IsScalarTower.algebraMap_eq K L M]

/-- Helper for Lemma 15.124.6: for extensions of valuation rings, weak unramifiedness is exactly
surjectivity of the value-group map, because injectivity comes from strict monotonicity. -/
private theorem weaklyUnramified_iff_surjective
    {A : Type*} {B : Type*}
    [CommRing A] [CommRing B] [Algebra A B]
    [IsDomain A] [ValuationRing A] [IsDomain B] [ValuationRing B]
    [IsExtensionOfValuationRings A B] :
    WeaklyUnramified A B ↔
      Function.Surjective
        (ValuativeExtension.mapValueGroupWithZero (FractionRing A) (FractionRing B)) := by
  let _ : FaithfulSMul A B := IsExtensionOfValuationRings.faithfulSMul (A := A) (B := B)
  constructor
  · intro h
    exact h.surjective
  · intro hsurj
    -- The value-group map is always strictly monotone, hence injective.
    refine ⟨ValuativeExtension.mapValueGroupWithZero_strictMono.injective, hsurj⟩

variable {A : Type u} [CommRing A] [IsDomain A] [ValuationRing A]
variable {Ah : Type u} [CommRing Ah] [Algebra A Ah] [IsHenselizationOf A Ah]

/-- Helper for Lemma 15.124.6: a local ring is already the localization at the complement of its
maximal ideal. -/
private theorem self_isLocalization_primeCompl_maximalIdeal
    (R : Type u) [CommRing R] [IsLocalRing R] :
    IsLocalization (maximalIdeal R).primeCompl R := by
  -- Elements outside the maximal ideal are exactly the units, so the identity map has the
  -- localization universal property.
  rw [isLocalization_iff]
  refine ⟨?_, ?_, ?_⟩
  · intro y
    exact IsLocalRing.notMem_maximalIdeal.mp y.2
  · intro z
    exact ⟨⟨z, 1⟩, by simp⟩
  · intro x y hxy
    exact ⟨1, by simpa using hxy⟩

/-- Helper for Lemma 15.124.6: localizing a local ring at its maximal ideal does not change the
ring. -/
private noncomputable abbrev local_ring_atMaximalIdeal_algEquiv
    (R : Type u) [CommRing R] [IsLocalRing R] :
    Localization.AtPrime (maximalIdeal R) ≃ₐ[R] R :=
  let _ : IsLocalization (maximalIdeal R).primeCompl R :=
    self_isLocalization_primeCompl_maximalIdeal R
  Localization.algEquiv (maximalIdeal R).primeCompl R

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
instance : IsExtensionOfValuationRings A Ah := by
  refine
    { toIsLocalHom := inferInstance
      algebraMap_injective := ?_ }
  -- The henselization map is faithfully flat, hence injective.
  exact RingHom.FaithfullyFlat.injective
    (algebraMap_faithfullyFlat_of_isHenselizationOf (R := A) (Rh := Ah))

/-- A henselization of a valuation ring is weakly unramified over the base valuation ring. -/
theorem henselization_weaklyUnramified : WeaklyUnramified A Ah := by
  -- Route correction: once the structural instance layer is supplied, the main theorem reduces to
  -- the source-faithful value-group surjectivity argument.
  rw [weaklyUnramified_iff_surjective (A := A) (B := Ah)]
  -- TODO: present `Ah` as the filtered colimit of closed-point étale branches, apply the stagewise
  -- weakly-unramified theorem to each localization, and factor a representative of any target
  -- value-group element through one branch to obtain a source preimage.
  sorry

variable {Ash : Type u} [CommRing Ash] [Algebra Ah Ash] [IsStrictHenselizationOf Ah Ash]

/-- A strict henselization over a henselization of a valuation ring is again a domain. -/
instance : IsDomain Ash := sorry

/-- A strict henselization over a henselization of a valuation ring is again a valuation ring. -/
instance : ValuationRing Ash := sorry

/-- The canonical map from a henselization of a valuation ring to a strict henselization over it
is an extension of valuation rings. -/
local instance strictHenselizationOverHenselization_isExtensionOfValuationRings :
    IsExtensionOfValuationRings Ah Ash := sorry

/-- A strict henselization over a henselization of a valuation ring is weakly unramified. -/
theorem strictHenselizationOverHenselization_weaklyUnramified :
    WeaklyUnramified Ah Ash := by
  -- Route correction: once the structural instance layer is supplied, the strict case again
  -- reduces to surjectivity of the value-group map via the closed-point colimit argument.
  rw [weaklyUnramified_iff_surjective (A := Ah) (B := Ash)]
  -- TODO: repeat the henselization argument over the valuation ring `Ah`, using the strict
  -- neighborhood presentation and stagewise weakly-unramified local branches.
  sorry

-- Proof sketch: combine the two canonical weakly unramified statements for the maps
-- `A → Ah` and `Ah → Ash`. The preceding instances record that both target rings remain valuation
-- rings and that both algebra maps are extensions of valuation rings.
/-- Lemma 15.124.6: if `A` is a valuation ring, `Ah` is a henselization of `A`, and `Ash` is a
strict henselization of `Ah`, then the inclusions `A ⊆ Ah` and `Ah ⊆ Ash` are extensions of
valuation rings and both are weakly unramified. -/
theorem henselization_tower_weaklyUnramified :
    WeaklyUnramified A Ah ∧ WeaklyUnramified Ah Ash := by
  exact ⟨henselization_weaklyUnramified, strictHenselizationOverHenselization_weaklyUnramified⟩

end
