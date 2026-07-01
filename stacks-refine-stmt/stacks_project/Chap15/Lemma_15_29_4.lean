import Mathlib.Algebra.Homology.Homotopy
import stacks_project.Chap15.Lemma_15_29_1

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open CategoryTheory.Limits
open AlgebraicTopology
open HomologicalComplex
open ZeroObject
open LocalizedModule

noncomputable section

universe u v

/-
Domain-style sampling:
- primary domain: localization families and the extended alternating Čech complex of an
  `R`-module;
- sampled owner declarations:
  `awayLocalizationFamilyMap`,
  `extendedAlternatingCechComplex`,
  `CategoryTheory.cechConerveRetraction_comp_coaugmentation_homotopic_id`,
  `CategoryTheory.CosimplicialObject.alternatingCofaceMapComplex_map_isHomotopyEquivalence`;
- best owner abstraction: the source-facing statement here is the contractibility of the canonical
  owner `extendedAlternatingCechComplex f M` under the unit-at-one-index hypothesis, while the
  split-mono and Čech-conerve homotopy machinery remains derived bridge data from the Chapter 10
  and Chapter 14 owners.

Primitive data is only the canonical localization-family map `awayLocalizationFamilyMap M f`.
The retraction of that map and the resulting homotopy-equivalence-to-zero statement are derived
API and should not be repackaged as new owners.
-/

section

variable {R : Type u} [CommRing R]
variable {M : Type (max u v)} [AddCommGroup M] [Module R M]
variable {r : ℕ}

/-- Scalar multiplication by an element of the powers of a unit is an invertible endomorphism of
an `R`-module. -/
private theorem powers_endomorphism_isUnit_of_isUnit (x : R) (hx : IsUnit x)
    (s : Submonoid.powers x) :
    IsUnit ((algebraMap R (Module.End R M)) s) := sorry

private abbrev awayLocalizationFamilyMapSection (f : Fin r → R) (i : Fin r)
    [Fact (IsUnit (f i))] :
    ModuleCat.of R (∀ j : Fin r, LocalizedModule.Away (f j) M) ⟶ ModuleCat.of R M :=
  ModuleCat.ofHom <|
    (LocalizedModule.lift (Submonoid.powers (f i)) (LinearMap.id)
        (powers_endomorphism_isUnit_of_isUnit (f i) (Fact.out : IsUnit (f i)))).comp
      (LinearMap.proj i)

-- Proof sketch: project to the `i`th factor and apply the localization universal property with
-- `g = LinearMap.id`; because `f i` is a unit, the resulting lift is inverse to
-- `LocalizedModule.mkLinearMap`, so the canonical localization-family map admits a retraction.
/-- If one entry `f i` is a unit, the canonical localization-family map is split mono. -/
theorem awayLocalizationFamilyMap_isSplitMono_of_isUnit_at (f : Fin r → R) (i : Fin r)
    (hi : IsUnit (f i)) :
    IsSplitMono (ModuleCat.ofHom (awayLocalizationFamilyMap M f)) := by
  letI : Fact (IsUnit (f i)) := ⟨hi⟩
  refine IsSplitMono.mk' ?_
  refine ⟨awayLocalizationFamilyMapSection f i, ?_⟩
  refine ModuleCat.hom_ext ?_
  ext m
  simp [awayLocalizationFamilyMapSection, awayLocalizationFamilyMap]

-- Proof sketch: `awayLocalizationFamilyMap_isSplitMono_of_isUnit_at` gives a retraction of the
-- canonical localization-family map. Lemma `14.28.5` then identifies the Čech conerve of this
-- split monomorphism as a cosimplicial retract of the constant cosimplicial object, and the
-- associated alternating complex is therefore homotopy equivalent to the single-term zero
-- complex.
/-- The extended alternating Čech complex is contractible as soon as one of the localizing
entries is a unit. -/
theorem extendedAlternatingCechComplex_homotopyEquivalent_zero_of_isUnit_at
    (f : Fin r → R) (i : Fin r) (hi : IsUnit (f i)) :
    Nonempty
      (HomotopyEquiv (extendedAlternatingCechComplex f M) 0) := sorry

-- Proof sketch: choose an index `i` for which `f i` is a unit and apply the indexed contractibility
-- statement.
/-- Lemma 15.29.4: if one of the localizing elements in the finite family `f` is a unit, then the
extended alternating Čech complex of the `R`-module `M` is homotopy equivalent to the zero
cochain complex. -/
theorem extendedAlternatingCechComplex_homotopyEquivalent_zero_of_exists_isUnit
    (f : Fin r → R) (hunit : ∃ i : Fin r, IsUnit (f i)) :
    Nonempty
      (HomotopyEquiv (extendedAlternatingCechComplex f M) 0) := by
  rcases hunit with ⟨i, hi⟩
  exact extendedAlternatingCechComplex_homotopyEquivalent_zero_of_isUnit_at f i hi

end
