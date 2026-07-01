import Mathlib
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.

universe u

open Polynomial

noncomputable section

variable {R S : Type u} [CommRing R] [CommRing S] [IsDomain R] [IsDomain S]
  [Algebra R S] [Module.IsTorsionFree R S] [IsIntegrallyClosed R]

local notation3 "K" => FractionRing R
local notation3 "L" => FractionRing S

attribute [local instance] FractionRing.liftAlgebra FractionRing.isScalarTower_liftAlgebra

/-
Domain triage:
* source-facing: the coefficientwise statement that the minimal polynomial over `FractionRing R`
  of an element integral over the normal domain `R` has coefficients in the image of `R`;
* core/canonical owner: `minpoly.isIntegrallyClosed_eq_field_fractions`, specialized to the
  fraction-field extension `FractionRing R ⊆ FractionRing S`;
* bridge/view: `coeff_map` turns the canonical polynomial identity into the textbook
  coefficientwise conclusion.
-/
recall minpoly.isIntegrallyClosed_eq_field_fractions

/-- Lemma 10.38.6: every coefficient of the minimal polynomial over `FractionRing R` of an element
integral over the normal domain `R` lies in the image of `R`. -/
theorem coeff_minpoly_mem_range_of_isIntegral (g : S) (hg : IsIntegral R g) (n : ℕ) :
    (minpoly K (algebraMap S L g)).coeff n ∈ Set.range (algebraMap R K) := by
  refine ⟨(minpoly R g).coeff n, ?_⟩
  rw [minpoly.isIntegrallyClosed_eq_field_fractions K L hg, coeff_map]
